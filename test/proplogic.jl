module PropLogic

using Rematch2: @match2
using TreeTransform: bottom_up_rewrite, TreeTransform
using Test

abstract type Expression end
struct And <: Expression
    x::Expression
    y::Expression
end
struct Or <: Expression
    x::Expression
    y::Expression
end
struct Not <: Expression
    x::Expression
end
struct Eq <: Expression
    x::Expression
    y::Expression
end
struct Impl <: Expression
    x::Expression
    y::Expression
end
struct True <: Expression end
struct False <: Expression end
struct Atom <: Expression
    name::String
end

function xform(node)
    @match2 node begin
        Not(True())      => False()
        Not(False())     => True()
        And(True(), x)   => x
        And(x, True())   => x
        And(False(), x)  => False()
        And(x, False())  => False()
        Or(True(), x)    => True()
        Or(x, True())    => True()
        Or(False(), x)   => x
        Or(x, False())   => x

        Impl(x, y) => Or(Not(x), y)
        Eq(x, y)   => And(Impl(x, y), Impl(y, x))

        Not(Not(x)) => x

        # DNF
        Not(And(x, y)) => Or(Not(x), Not(y))
        Not(Or(x, y))  => And(Not(x), Not(y))
        And(Or(x, y), z) => Or(And(x, z), And(y, z))
        And(z, Or(x, y)) => Or(And(z, x), And(z, y))

        x => x
    end
end

function simplify(node)
    bottom_up_rewrite(xform, node)
end

@testset "Check some simple cases" begin
    @test simplify(Not(True())) == False()
    @test simplify(Impl(False(), Atom("x"))) == True()
    @test simplify(Not(Not(Atom("x")))) == Atom("x")
    @test simplify(And(Or(Atom("x"), Atom("y")), Atom("z"))) == Or(And(Atom("x"), Atom("z")), And(Atom("y"), Atom("z")))
end

end
