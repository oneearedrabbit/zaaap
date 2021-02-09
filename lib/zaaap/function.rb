class Function
  def initialize(scope, params, body)
    @scope = scope
    @params = params
    @body = body
  end

  def call(scope, cells)
    closure = @params.inject(Scope.new(@scope)) do |res, name|
      res[name] = cells.shift
      res
    end

    closure[:scope] = scope

    @body.map { |e| e.eval(closure) }.last
  end

  def expand
    p @body
    p @params
    # p @scope
  end
end

class Syntax
  def initialize(&block)
    @body = block
  end

  def call(scope, cells)
    @body.call(scope, cells)
  end
end
