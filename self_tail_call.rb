# Pretty RBC
# Copyright (c) 2008 Jeremy Roach
# Licensed under The MIT License

module SelfTailCall

  def self.call_to_goto(ic, index, ins_size)
    if ins_size >= 2
      ic.replace(index, :goto, 99999)
      ic.delete(index + 2, ins_size - 2)
    else
      raise "error: call_to_goto: small ins_size"
    end
  end

  def self.get_arg_counts(tail_calls)
    tail_calls.inject([]) do |arg_counts, info|
      arg_counts << info[1]
    end
  end

  def self.modify_iseq_copy(ic, num_args, uniq_arg_counts,
                                len_orig_iseq, len_orig_exc, len_orig_lines)

    ic.excludes = []
    uniq_arg_counts.each_value do |v|
      ic.excludes << v
    end

    len_iseq = ic.iseq.length
    len_exc = ic.exceptions.length
    len_lines = ic.lines.length

    ic.duplicate_iseq(0...len_orig_iseq)
    ic.offset_gotos(len_iseq...ic.iseq.length)

    ic.duplicate_exceptions(0...len_orig_exc)
    ic.offset_exceptions(len_exc...ic.exceptions.length, len_iseq)

    ic.duplicate_lines(0...len_orig_lines)
    ic.offset_lines(len_lines...ic.lines.length, len_iseq)

    i = len_iseq
    while i
      if ic.iseq[i] == :passed_arg
        k = ic.iseq[i.succ]
        ic.delete(i.succ)

        if k < num_args
          ic.replace(i, :push_true)
        else
          ic.replace(i, :push_false)
        end

      elsif ic.iseq[i] == :set_local_from_fp
        ic.replace(i, :set_local)
        ic.replace(i + 2, :pop)
      end
      i = ic.next(i)
    end

    ic.normalize_gotos
  end

  def self.modify_instructions(ic, tail_calls)
    arg_counts = get_arg_counts(tail_calls)
    uniq_arg_counts = {}

    len_orig_iseq = ic.iseq.length
    len_orig_exc = ic.exceptions.length
    len_orig_lines = ic.lines.length

    tail_calls.each do |info|
      index, num_args = info
      if uniq_arg_counts[num_args]
        ic.iseq[index.succ] = uniq_arg_counts[num_args]
      else
        uniq_arg_counts[num_args] = ic.iseq.length
        ic.iseq[index.succ] = uniq_arg_counts[num_args]
        modify_iseq_copy(ic, num_args, uniq_arg_counts,
                            len_orig_iseq, len_orig_exc, len_orig_lines)
      end
    end

    ic.iseq = ic.iseq[0...len_orig_iseq]
    ic.exceptions = ic.exceptions[0...len_orig_exc]
    ic.lines = ic.lines[0...len_orig_lines]

    arg_counts.uniq.each do |num_args|
      modify_iseq_copy(ic, num_args, uniq_arg_counts,
                            len_orig_iseq, len_orig_exc, len_orig_lines)
    end
  end

  def self.to_return?(iseq, k)
    case iseq[k]
    when :goto
      to_return?(iseq, iseq[k.succ])
    when :sret
      true
    else
      false
    end
  end

  def self.find(ic, offset = 0)
    i = offset

    while i
      if ic.iseq[i] == :send_stack and
            ic.cm.name == ic.literals[ic.iseq[i.succ]].name and
            to_return?(ic.iseq, ic.next(i))
        num_args = ic.iseq[i + 2]
        back1 = ic.previous(i)
        back2 = ic.previous(back1)

        if ic.iseq[back1] == :push_self
          return [back1, 4, num_args]
        elsif ic.iseq[back1] == :set_call_flags and ic.iseq[back2] == :push_self
          return [back2, 6, num_args]
        end
      end
      i = ic.next(i)
    end

    [nil, nil, nil]
  end

  def self.optimize(cm_main)

    for cm in cm_main.all_methods
      tail_calls = []
      ic = InstructionChanges.new(cm)
      index, ins_size, num_args = find(ic)

      unless index.nil?
        until index.nil?
          tail_calls << [index, num_args]
          call_to_goto(ic, index, ins_size)
          index, ins_size, num_args = find(ic, index)
        end

        modify_instructions(ic, tail_calls)
        ic.finalize
      end
    end
  end
end

