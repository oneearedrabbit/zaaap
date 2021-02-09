module Frankenstein
  class Program < Treetop::Runtime::SyntaxNode
    def eval(scope)
      elements.map { |e| e.eval(scope) }.last
    end

    def inspect
      elements.map { |x| x.text_value }.join
    end
  end

  class Cell < Treetop::Runtime::SyntaxNode
    def data
      elements[1]
    end

    def eval(scope)
      data.eval(scope)
    end

    def inspect
      elements.map { |x| x.to_s }.join
    end
  end

  module Integer
    def eval(scope)
      text_value.to_i
    end

    def inspect
      text_value
    end
  end

  module Boolean
    def eval(scope)
      text_value == '#t'
    end

    def inspect
      text_value
    end
  end

  class List < Treetop::Runtime::SyntaxNode
    def cells
      elements[1].elements.map { |e| e.data }
    end

    def eval(scope)
      function = cells[0].eval(scope)
      args = cells[1..-1]
      function.call(scope, args)
    end

    def inspect
      elements.map { |x| x.text_value }.join
    end

    def expand
      elements.map { |x| x.text_value }.join
    end
  end

  class Identifier < Treetop::Runtime::SyntaxNode
    def eval(scope)
      scope[text_value]
    end

    def inspect
      text_value
    end

    def expand
      p text_value
    end
  end

  class String < Treetop::Runtime::SyntaxNode
    def eval(scope)
      Kernel.eval(text_value)
    end

    def inspect
      text_value
    end
  end
end
