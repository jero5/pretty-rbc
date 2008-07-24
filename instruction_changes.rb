# Pretty RBC
# Copyright (c) 2008 Jeremy Roach
# Licensed under The MIT License

class Array

  def to_tup
    tup = Tuple.new(size)
    each_index do |i|
      tup[i] = self[i]
    end
    tup
  end
end

class CompiledMethod

  def all_methods(obj = self)
    case obj
    when CompiledMethod
      cmethods = [obj]
      obj.literals.each do |elem|
        cmethods += all_methods(elem)
      end
      cmethods
    else
      []
    end
  end

  def compile_all
    all_methods.each do |cm|
      cm.compile
    end
  end
end

class InstructionChanges
  attr_accessor :cm, :iseq, :literals, :exceptions, :lines
  attr_accessor :excludes  # goto arg values not to modify

  INSTRUCTIONS_WITH_LOCAL = {
    :push_local => 0, :set_local => 0, :push_local_depth => 1,
    :set_local_depth => 1, :set_local_from_fp => 0
  }

  INSTRUCTIONS_WITH_LITERAL = {
    :push_literal => 0, :set_ivar => 0, :push_ivar => 0,
    :push_const => 0, :set_const => 0, :set_const_at => 0,
    :find_const => 0, :attach_method => 0, :add_method => 0,
    :open_class => 0, :open_class_under => 0, :open_module => 0,
    :open_module_under => 0, :send_method => 0, :send_stack => 0,
    :send_stack_with_block => 0, :send_with_arg_register => 0,
    :send_super_stack_with_block => 0, :send_super_with_arg_register => 0,
    :set_literal => 0, :check_serial => 0, :dummy => 1
  }

  def initialize(cm)
    @cm = cm
    @iseq = cm.bytecodes.decode.flatten
    @literals = cm.literals.to_a
    @exceptions = cm.exceptions.to_a.map { |tup| tup.to_a }
    @lines = cm.lines.to_a.map { |tup| tup.to_a }
    @excludes = []
  end

  def finalize
    encoder = InstructionSequence::Encoder.new
    layered_iseq = InstructionChanges.wrap(@iseq)

    @cm.bytecodes = encoder.encode_stream(layered_iseq)
    @cm.literals = @literals.to_tup
    @cm.exceptions = @exceptions.map { |arr| arr.to_tup }.to_tup
    @cm.lines = @lines.map { |arr| arr.to_tup }.to_tup
  end

  def at_goto?(i)
    [:goto, :goto_if_true, :goto_if_false, :goto_if_defined].include? @iseq[i]
  end

  def at_ins_with_local?(i)
    INSTRUCTIONS_WITH_LOCAL[@iseq[i]]
  end

  def at_ins_with_literal?(i)
    INSTRUCTIONS_WITH_LITERAL[@iseq[i]]
  end

  def previous(i)
    return nil if i == 0
    k = i - 1
    k -= 1 while @iseq[k].kind_of? Integer
    k
  end

  def next(i)
    k = i + 1
    return nil if k >= @iseq.length
    while @iseq[k].kind_of? Integer
      k += 1
      return nil if k >= @iseq.length
    end
    k
  end

  def insert(i, values)
    oldsize = @iseq.length

    if i < 0
      i += oldsize.succ
    end

    @iseq.insert(i, *values)

    newsize = @iseq.length
    size_diff = newsize - oldsize

    recalculate_gotos(:insert, i, size_diff)
    recalculate_exceptions(:insert, i, size_diff)
    recalculate_lines(:insert, i, size_diff)
  end

  def replace(i, *values)
    if i < 0 or i + values.length > @iseq.length
      raise "error: replace: out of bounds"
    end

    values.each_index do |k|
      @iseq[i] = values[k]
      i += 1
    end
  end

  def delete(i, ins_size = nil)
    oldsize = @iseq.length

    if i < 0
      i += oldsize
    end

    if ins_size
      ins_size.times { @iseq.delete_at(i) }
    elsif @iseq[i].kind_of? Integer
      @iseq.delete_at(i)
    else
      @iseq.delete_at(i)
      @iseq.delete_at(i) while @iseq[i].kind_of? Integer
    end

    newsize = @iseq.length
    size_diff = oldsize - newsize

    recalculate_gotos(:delete, i, size_diff)
    recalculate_exceptions(:delete, i, size_diff)
    recalculate_lines(:delete, i, size_diff)
  end

  def recalculate_gotos(action, i, size_diff)
    return if size_diff == 0
    k = i + (size_diff - 1)

    @iseq.each_index do |n|

      if at_goto? n
        x = @iseq[n.succ]
        unless @excludes.include? x
          case action
          when :delete
            if normalized_goto(x) > k
              @iseq[n.succ] = x - size_diff
            end
          when :insert
            if normalized_goto(x) >= i and (n < i or n > k)
              @iseq[n.succ] = x + size_diff
            end
          end
        end
      end
    end
  end

  def duplicate_iseq(range)
    @iseq += @iseq[range]
  end

  def offset_gotos(range)
    first_index = range.first

    for i in range
      if at_goto? i
        k = @iseq[i.succ]
        unless @excludes.include? k
          @iseq[i.succ] = k + first_index + 100_000_000
        end
      end
    end
  end

  # use after offset_gotos + delete/insert
  #
  def normalize_gotos

    @iseq.each_index do |i|

      if at_goto? i
        k = @iseq[i.succ]
        @iseq[i.succ] = normalized_goto(k)
      end
    end
  end

  def normalized_goto(num)
    if num - 100_000_000 >= 0
      num - 100_000_000
    else
      num
    end
  end

  def recalculate_exceptions(action, i, size_diff)
    return if size_diff == 0
    k = i + (size_diff - 1)

    n = 0
    while n < @exceptions.length
      first, last, other = @exceptions[n]

      raise "error: recalculate_exceptions: garbage '#{@cm.name}'" unless
        other > last and last >= first

      case action
      when :delete

        if first >= i and last <= k
          @exceptions.delete_at(n)
          n -= 1
        elsif first >= i and first <= k
          @exceptions[n] = [i, last - size_diff, other - size_diff]
        elsif first < i and last >= i and last <= k
          if other > k
            @exceptions[n] = [first, i - 1, other - size_diff]
          else
            @exceptions[n] = [first, i - 1, i]
          end
        elsif first < i and last > k
          @exceptions[n] = [first, last - size_diff, other - size_diff]
        elsif first > k and last > k
          @exceptions[n] = [first - size_diff, last - size_diff, other - size_diff]
        elsif other >= i and other <= k
          @exceptions[n] = [first, last, i]
        end
      when :insert

        new_first = (first >= i ? first + size_diff : first)
        new_last  = (last >= i ? last + size_diff : last)
        new_other = (other >= i ? other + size_diff : other)

        @exceptions[n] = [new_first, new_last, new_other]
      end

      n += 1
    end
  end

  def duplicate_exceptions(range)
    for i in range
      first, last, other = @exceptions[i]
      @exceptions << [first, last, other]
    end
  end

  def offset_exceptions(range, offset)
    for i in range
      first, last, other = @exceptions[i]
      @exceptions[i] = [first + offset, last + offset, other + offset]
    end
  end

  def recalculate_lines(action, i, size_diff)
    return if size_diff == 0
    k = i + (size_diff - 1)

    n = 0
    while n < @lines.length
      first, last, other = @lines[n]

      if first > last
        @lines.delete_at(n)
        next
      end

      case action
      when :delete

        if first >= i and last <= k
          @lines.delete_at(n)
          n -= 1
        elsif first >= i and first <= k
          @lines[n] = [i, last - size_diff, other]
        elsif first < i and last >= i and last <= k
          @lines[n] = [first, i - 1, other]
        elsif first < i and last > k
          @lines[n] = [first, last - size_diff, other]
        elsif first > k and last > k
          @lines[n] = [first - size_diff, last - size_diff, other]
        end
      when :insert

        new_first = (first >= i ? first + size_diff : first)
        new_last  = (last >= i ? last + size_diff : last)

        @lines[n] = [new_first, new_last, other]
      end

      n += 1
    end
  end

  def duplicate_lines(range)
    for i in range
      first, last, other = @lines[i]
      @lines << [first, last, other]
    end
  end

  def offset_lines(range, offset)
    for i in range
      first, last, other = @lines[i]
      @lines[i] = [first + offset, last + offset, other]
    end
  end

  def insert_literal(i, values)
    oldsize = @literals.length

    if i < 0
      i += oldsize.succ
    end

    @literals.insert(i, *values)

    newsize = @literals.length
    size_diff = newsize - oldsize

    recalculate_literals(:insert, i, size_diff)
  end

  def replace_literal(i, *values)
    if i < 0 or i + values.length > @literals.length
      raise "error: replace_literal: out of bounds"
    end

    values.each_index do |k|
      @literals[i] = values[k]
      i += 1
    end
  end

  def delete_literal(i, num_del = 1)
    oldsize = @literals.length

    if i < 0
      i += oldsize
    end

    num_del.times { @literals.delete_at(i) }

    newsize = @literals.length
    size_diff = oldsize - newsize

    recalculate_literals(:delete, i, size_diff)
  end

  def recalculate_literals(action, i, size_diff)
    return if size_diff == 0
    k = i + (size_diff - 1)

    @iseq.each_index do |n|

      if arg_idx = at_ins_with_literal?(n)
        x = @iseq[n.succ + arg_idx]
        case action
        when :delete
          if x > k
            @iseq[n.succ + arg_idx] = x - size_diff
          end
        when :insert
          if x >= i
            @iseq[n.succ + arg_idx] = x + size_diff
          end
        end
      end
    end
  end

  def offset_literals(range, offset)
    for i in range
      if arg_idx = at_ins_with_literal?(i)
        k = @iseq[i.succ + arg_idx]
        @iseq[i.succ + arg_idx] = k + offset
      end
    end
  end

  def offset_locals(range, offset)
    for i in range
      if arg_idx = at_ins_with_local?(i)
        k = @iseq[i.succ + arg_idx]
        @iseq[i.succ + arg_idx] = k + offset
      end
    end
  end

  def self.wrap(iseq)
    layered_iseq = []
    arr = []

    iseq.each_index do |i|

      case iseq[i]
      when Symbol
        if arr.length == 0
          arr << iseq[i]
        else
          layered_iseq << arr
          arr = [iseq[i]]
        end
      when Integer
        arr << iseq[i]
      else
        raise "error: InstructionChanges.wrap: bad object type '#{iseq[i].class}'"
      end
    end

    if arr.length == 0
      layered_iseq
    else
      layered_iseq << arr
    end
  end

  def test

    encoder = InstructionSequence::Encoder.new
    cm = CompiledMethod.new
    cm.bytecodes = encoder.encode_stream([[:passed_arg, 10], [:push_true]])
    ic = InstructionChanges.new(cm)

    ic.iseq = [:foo, 10, :hi]
    ic.literals = []
    ic.exceptions = []
    ic.lines = []

    raise "fail 0" unless ic.next(0) == 2
    raise "fail 1" unless ic.previous(2) == 0

    ic.delete(0)
    raise "fail 2" unless ic.iseq[0] == :hi

    ic.insert(0, [:goto, 25])
    raise "fail 3" unless ic.iseq == [:goto, 25, :hi]

    ic.replace(1, 2)
    raise "fail 4" unless ic.iseq == [:goto, 2, :hi]

    ic.insert(-1, [:hello, 10, 20, :what, :goto_if_true, 7, :hey, :goto, 0])
    raise "fail 5" unless
      ic.iseq == [:goto, 2, :hi, :hello, 10, 20, :what, :goto_if_true, 7, :hey, :goto, 0]

    ic.delete(3)
    raise "fail 6" unless
      ic.iseq == [:goto, 2, :hi, :what, :goto_if_true, 4, :hey, :goto, 0]

    ic.delete(0)
    raise "fail 7" unless ic.iseq == [:hi, :what, :goto_if_true, 2, :hey, :goto, 0]

    ic.replace(6, 4)
    raise "fail 8" unless ic.iseq == [:hi, :what, :goto_if_true, 2, :hey, :goto, 4]

    ic.delete(2)
    raise "fail 9" unless ic.iseq == [:hi, :what, :hey, :goto, 2]

    ic.delete(0)
    raise "fail 10" unless ic.iseq == [:what, :hey, :goto, 1]

    ic.insert(0, [:goto, 2])
    raise "fail 11" unless ic.iseq == [:goto, 2, :what, :hey, :goto, 3]

    ic.insert(2, [:foo])
    raise "fail 12" unless ic.iseq == [:goto, 3, :foo, :what, :hey, :goto, 4]

    ic.delete(3)
    raise "fail 13" unless ic.iseq == [:goto, 3, :foo, :hey, :goto, 3]

    ic.delete(8)
    raise "fail 14" unless ic.iseq == [:goto, 3, :foo, :hey, :goto, 3]

    ic.insert(8, [:oh])
    raise "fail 15" unless ic.iseq == [:goto, 3, :foo, :hey, :goto, 3, nil, nil, :oh]

    ic.iseq = [:goto, 2, :foo, :hi, :goto, 3, :goto_if_false, 4, :where, :goto, 8]

    ic.insert(-1, ic.iseq)
    raise "fail 16" unless
      ic.iseq == [:goto, 2, :foo, :hi, :goto, 3, :goto_if_false, 4, :where, :goto, 8,
                  :goto, 2, :foo, :hi, :goto, 3, :goto_if_false, 4, :where, :goto, 8]

    ic.replace(18, 11)
    raise "fail 17" unless
      ic.iseq == [:goto, 2, :foo, :hi, :goto, 3, :goto_if_false, 4, :where, :goto, 8,
                  :goto, 2, :foo, :hi, :goto, 3, :goto_if_false, 11, :where, :goto, 8]

    ic.excludes = [11]
    ic.offset_gotos(11..21)
    ic.normalize_gotos
    raise "fail 18" unless
      ic.iseq == [:goto, 2, :foo, :hi, :goto, 3, :goto_if_false, 4, :where, :goto, 8,
                  :goto, 13, :foo, :hi, :goto, 14, :goto_if_false, 11, :where, :goto, 19]

    ic.iseq = [:hi, 1, :why, 10]
    raise "fail 19" unless ic.previous(0).nil?
    raise "fail 20" unless ic.next(2).nil?

    ic.excludes = [6]
    ic.iseq = [:goto, 3, :hello, :hi, :goto_if_true, 6, :foo, :when]

    ic.delete(2)
    raise "fail 21" unless
      ic.iseq == [:goto, 2, :hi, :goto_if_true, 6, :foo, :when]

    ic.excludes = []
    ic.iseq = [:here, 5, :where, 10]
    ic.replace(1, 8, :when)
    raise "fail 22" unless ic.iseq == [:here, 8, :when, 10]

    ic.delete(0, 3)
    raise "fail 23" unless ic.iseq == [10]

    ic.iseq = [:hi, 1, :why, 10, :foo]
    raise "fail 24" unless
      InstructionChanges.wrap(ic.iseq) == [[:hi, 1], [:why, 10], [:foo]]

    ic.iseq = [:goto, 2, :here, :foo, 10, :goto, 7, :what]
    ic.offset_gotos(0..7)
    ic.delete(3)
    ic.insert(3, [:foo])
    ic.insert(0, [:huh])
    ic.normalize_gotos
    raise "fail 24.1" unless ic.iseq == [:huh, :goto, 3, :here, :foo, :goto, 7, :what]

    ic.iseq = [:a, :b, :c, :d, :e, :f, :g, :h, :i, :j, :k, :l,
               :m, :n, :o, :p, :q, :r, :s, :t, :u, :v, :w, :x, :y, :z]
    ic.exceptions = [[0, 2, 24], [3, 7, 8], [9, 19, 22], [20, 20, 21]]

    ic.delete(0, 3)
    raise "fail 25" unless ic.exceptions == [[0, 4, 5], [6, 16, 19], [17, 17, 18]]

    ic.delete(6, 2)
    raise "fail 26" unless ic.exceptions == [[0, 4, 5], [6, 14, 17], [15, 15, 16]]

    ic.delete(14, 4)
    raise "fail 27" unless ic.exceptions == [[0, 4, 5], [6, 13, 14]]

    ic.delete(13)
    raise "fail 28" unless ic.exceptions == [[0, 4, 5], [6, 12, 13]]

    ic.delete(8, 2)
    raise "fail 29" unless ic.exceptions == [[0, 4, 5], [6, 10, 11]]

    ic.delete(3)
    raise "fail 30" unless ic.exceptions == [[0, 3, 4], [5, 9, 10]]

    ic.delete(4)
    raise "fail 31" unless ic.exceptions == [[0, 3, 4], [4, 8, 9]]

    ic.insert(4, [:a, :b])
    raise "fail 32" unless ic.exceptions == [[0, 3, 6], [6, 10, 11]]

    ic.insert(12, [:foo])
    raise "fail 33" unless ic.exceptions == [[0, 3, 6], [6, 10, 11]]
    raise "fail 34" unless
      ic.iseq == [:d, :e, :f, :h, :a, :b, :l, :m, :p, :q, :r, :x, :foo, :y, :z]

    ic.duplicate_exceptions(0..0)
    raise "fail 35" unless ic.exceptions == [[0, 3, 6], [6, 10, 11], [0, 3, 6]]

    ic.offset_exceptions(1..2, 3)
    raise "fail 36" unless ic.exceptions == [[0, 3, 6], [9, 13, 14], [3, 6, 9]]

    ic.iseq = [:a, :b, :c, :d, :e, :f, :g, :h, :i, :j, :k, :l,
               :m, :n, :o, :p, :q, :r, :s, :t, :u, :v, :w, :x, :y, :z]
    ic.lines = [[0, 2, 24], [3, 7, 8], [9, 19, 22], [20, 20, 21]]

    ic.delete(0, 3)
    raise "fail 37" unless ic.lines == [[0, 4, 8], [6, 16, 22], [17, 17, 21]]

    ic.delete(6, 2)
    raise "fail 38" unless ic.lines == [[0, 4, 8], [6, 14, 22], [15, 15, 21]]

    ic.delete(14, 4)
    raise "fail 39" unless ic.lines == [[0, 4, 8], [6, 13, 22]]

    ic.delete(13)
    raise "fail 40" unless ic.lines == [[0, 4, 8], [6, 12, 22]]

    ic.delete(8, 2)
    raise "fail 41" unless ic.lines == [[0, 4, 8], [6, 10, 22]]

    ic.delete(3)
    raise "fail 42" unless ic.lines == [[0, 3, 8], [5, 9, 22]]

    ic.delete(4)
    raise "fail 43" unless ic.lines == [[0, 3, 8], [4, 8, 22]]

    ic.insert(4, [:a, :b])
    raise "fail 44" unless ic.lines == [[0, 3, 8], [6, 10, 22]]

    ic.insert(12, [:foo])
    raise "fail 45" unless ic.lines == [[0, 3, 8], [6, 10, 22]]
    raise "fail 46" unless
      ic.iseq == [:d, :e, :f, :h, :a, :b, :l, :m, :p, :q, :r, :x, :foo, :y, :z]

    ic.duplicate_lines(0..0)
    raise "fail 47" unless ic.lines == [[0, 3, 8], [6, 10, 22], [0, 3, 8]]

    ic.offset_lines(1..2, 3)
    raise "fail 48" unless ic.lines == [[0, 3, 8], [9, 13, 22], [3, 6, 8]]

    ic.iseq = [:a, :b, :c, :d, :e, :f, :g, :h, :i, :j, :k, :l, :m]
    ic.exceptions = [[8, 9, 10]]
    ic.lines = [[9, 10, 50]]

    ic.duplicate_iseq(4..5)
    raise "fail 49" unless
      ic.iseq = [:a, :b, :c, :d, :e, :f, :g, :h, :i, :j, :k, :l, :m, :e, :f]
    raise "fail 50" unless ic.exceptions = [[8, 9, 10]]
    raise "fail 51" unless ic.lines = [[9, 10, 50]]

    ic.iseq = [:push_literal, 2, :goto, 4, :foo, :dummy, 99, 3]
    ic.literals = [:hello, :hi, :hey, :howdy]

    ic.insert_literal(2, [:oh, :no])
    raise "fail 52" unless ic.iseq == [:push_literal, 4, :goto, 4, :foo, :dummy, 99, 5]
    raise "fail 53" unless ic.literals == [:hello, :hi, :oh, :no, :hey, :howdy]

    ic.insert_literal(-1, [:foo])
    raise "fail 54" unless ic.iseq == [:push_literal, 4, :goto, 4, :foo, :dummy, 99, 5]
    raise "fail 55" unless ic.literals == [:hello, :hi, :oh, :no, :hey, :howdy, :foo]

    ic.insert_literal(0, [:blah])
    raise "fail 56" unless ic.iseq == [:push_literal, 5, :goto, 4, :foo, :dummy, 99, 6]
    raise "fail 57" unless ic.literals == [:blah, :hello, :hi, :oh, :no, :hey, :howdy, :foo]

    ic.delete_literal(1, 2)
    raise "fail 58" unless ic.iseq == [:push_literal, 3, :goto, 4, :foo, :dummy, 99, 4]
    raise "fail 59" unless ic.literals == [:blah, :oh, :no, :hey, :howdy, :foo]

    ic.delete_literal(-1)
    raise "fail 60" unless ic.iseq == [:push_literal, 3, :goto, 4, :foo, :dummy, 99, 4]
    raise "fail 61" unless ic.literals == [:blah, :oh, :no, :hey, :howdy]

    ic.delete_literal(2)
    raise "fail 62" unless ic.iseq == [:push_literal, 2, :goto, 4, :foo, :dummy, 99, 3]
    raise "fail 63" unless ic.literals == [:blah, :oh, :hey, :howdy]

    ic.delete_literal(2)
    raise "fail 64" unless ic.iseq == [:push_literal, 2, :goto, 4, :foo, :dummy, 99, 2]
    raise "fail 65" unless ic.literals == [:blah, :oh, :howdy]

    ic.offset_literals(0..0, 17)
    raise "fail 66" unless ic.iseq == [:push_literal, 19, :goto, 4, :foo, :dummy, 99, 2]
    raise "fail 67" unless ic.literals == [:blah, :oh, :howdy]

    ic.iseq = [:push_local, 0, :goto, 4, :foo, :dummy, 99, 3]

    ic.offset_locals(0..1, 33)
    raise "fail 68" unless ic.iseq == [:push_local, 33, :goto, 4, :foo, :dummy, 99, 3]

    ic.literals = [:hi, :hello, :hey, :howdy]

    ic.replace_literal(1, :oh, :no)
    raise "fail 69" unless ic.literals == [:hi, :oh, :no, :howdy]

    ic.iseq = [:set_local_depth, 2, 3, :foo, :set_literal, 3]
    raise "fail 70" unless ic.at_ins_with_literal?(4) == 0
    raise "fail 71" unless ic.at_ins_with_local?(0) == 1
    raise "fail 72" unless ic.at_ins_with_literal?(3) == nil
    raise "fail 73" unless ic.at_ins_with_local?(3) == nil
  end
end

