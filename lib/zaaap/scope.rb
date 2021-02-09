class Scope
  attr_reader :symbols

  def initialize(parent = nil)
    @parent  = parent
    @symbols = {}
  end

  def [](name)
    begin
      symbol = @symbols.has_key?(name) ? @symbols[name] : @parent[name]
    rescue => e
      puts "ERROR: Unbound variable '#{name}'"
    end

    # we are going to get a value of a variable, so we must evaluate
    # it. quite logical, isn'it?
    if [Frankenstein::List,
        Frankenstein::Identifier,
        Treetop::Runtime::SyntaxNode].include?(symbol.class)
      symbol.eval(@symbols[:scope])
    else
      symbol
    end
  end

  def []=(name, value)
    @symbols[name] = value
  end

  def syntax(name, &block)
    self[name] = Syntax.new(&block)
  end
end

class TopLevel < Scope
  def initialize
    super

    syntax('lambda') do |scope, cells|
      names = cells[0].cells.map { |e| e.text_value }
      body = cells[1..-1]
      Function.new(scope, names, body)
    end

    syntax('define') do |scope, cells|
      scope[cells[0].text_value] = cells[1].eval(scope)
    end

    # TODO: define* function which evaluats its second
    # argument before beta-reduction

    syntax('+') do |scope, cells|
      cells.inject(cells.shift.eval(scope)) { |res, cell| res + cell.eval(scope) }
    end

    # syntax('display') do |scope, cells|
    #   # TODO: I would like to have a generic print function, w/o this
    #   # separation disps, dispn, dispb, etc
    #   function = cells.shift.eval(scope)
    #   function.call(scope, cells)
    # end

    syntax('display') do |scope, cells|
      print cells.map { |c| c.eval(scope) }.join
    end

    syntax('dispb') do |scope, cells|
      dispb = "(lambda (x) ((x #t) #f))"
      function = Corpse.parse(dispb).eval(TopLevel.new)
      print function.call(scope, cells)
    end

    syntax('dispn') do |scope, cells|
      dispn = "(lambda (n) ((n (lambda (x) (+ 1 x))) 0))"
      function = Corpse.parse(dispn).eval(TopLevel.new)
      print function.call(scope, cells)
    end

    syntax('expand') do |scope, cells|
      fn = cells[0].text_value
      puts scope[fn].expand
    end

    # TODO: implement "load" method
    # syntax('load') do |scope, cells|
    #   path = File.expand_path(cells[0].eval(scope))
    #   content = path.read
    #   tree = Corpse.parse(content)
    #   # include tree to the main branch
    # end
  end
end
