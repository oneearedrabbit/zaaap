require 'rubygems'
require 'rake/testtask'
require 'rcov'
require 'rcov/rcovtask'

task :default => [:test]

lib_dir = File.expand_path('lib')
test_dir = File.expand_path('test')

Rake::TestTask.new("test") do |t|
  t.libs = [lib_dir, test_dir]
  t.pattern = 'test/unit/test_*.rb'
  t.warning = true
end

namespace :test do
  namespace :coverage do
    desc "Delete aggregate coverage data."
    task(:clean) { rm_f "coverage.data" }
  end
  desc 'Aggregate code coverage for unit, functional and integration tests'
  task :coverage => "test:coverage:clean"
  %w[unit].each do |target|
    namespace :coverage do
      Rcov::RcovTask.new(target) do |t|
        t.libs << "test"
        t.test_files = FileList["test/#{target}/test_*.rb"]
        t.output_dir = "test/coverage/#{target}"
        t.verbose = true
        t.rcov_opts << '--rails --aggregate coverage.data --exclude /gems/'
      end
    end
    task :coverage => "test:coverage:#{target}"
  end
end
