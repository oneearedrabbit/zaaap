require 'rubygems'
require 'treetop'

Treetop.load File.dirname(__FILE__) + '/frankenstein.treetop'
%w[frankenstein scope function].each { |path| require File.dirname(__FILE__) + '/' + path }

module Corpse
  def self.run(content)
    tree = parse(content)
    tree.eval(TopLevel.new)
  end

  def self.parse(string)
    @parser ||= FrankensteinParser.new
    @parser.parse(string)
  end
end
