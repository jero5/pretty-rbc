
SELF_DIR = File.dirname(__FILE__) + '/'

require "#{SELF_DIR}pcm.rb"
require "#{SELF_DIR}instruction_changes.rb"
require "#{SELF_DIR}self_tail_call.rb"
require "#{SELF_DIR}playground.rb"

module Main

  def self.infinite_dump_and_load_self

    cm = MethodContext.current.method
    str = PrettyCM.dump(cm)
    cm = PrettyCM.load(str)
    PrettyCM.write_file("#{SELF_DIR}main.pcm", str)
    puts "object_id: '#{cm.object_id}'"
    sleep(65)
    cm.as_script
  end

  def self.dump_others

    recurse = true
    src_dir  = ''
    dest_dir = ''
    activate_dest_dir = false
    activate_load = false

    PrettyCM.fetch_files(src_dir, recurse) do |file|
      if file =~ / \.rb \Z /x
        if file =~ / . /x
          cm = Compile.compile_file(file)
          str = PrettyCM.dump(cm)

          if activate_load
            cm = PrettyCM.load(str)
            str = PrettyCM.dump(cm)
          end

          file = PrettyCM.replace_suffix(file, '.rb', '.pcm')

          if activate_dest_dir
            file = dest_dir + file.gsub('/', '_')
          end

          if PrettyCM.read_file(file) != str
            PrettyCM.write_file(file, str)
            print "\n#{file}"
          else
            print '.'
          end
        end
      end
    end

    puts ''
  end
end

#Main.infinite_dump_and_load_self
#Main.dump_others

cm = MethodContext.current.method
ic = InstructionChanges.new(cm)
ic.test

cm = Compile.compile_file("#{SELF_DIR}test_tail_call.rb")
SelfTailCall.optimize(cm)
#str = PrettyCM.dump(cm)
#PrettyCM.write_file("#{SELF_DIR}test_tail_call.pcm", str)

cm.as_script

