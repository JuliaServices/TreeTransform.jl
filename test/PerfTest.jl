module PerfTest

using AutoHashEqualsCached

#
# This file is not run during testing, but it is used as a metric of performance
# for our tree transoformation package.
#

using TreeTransform
using Rematch2

abstract type Expression end
@auto_hash_equals_cached struct Add <: Expression
    x::Expression
    y::Expression
end
@auto_hash_equals_cached struct Sub <: Expression
    x::Expression
    y::Expression
end
@auto_hash_equals_cached struct Neg <: Expression
    x::Expression
end
@auto_hash_equals_cached struct Mul <: Expression
    x::Expression
    y::Expression
end
@auto_hash_equals_cached struct Div <: Expression
    x::Expression
    y::Expression
end
@auto_hash_equals_cached struct Const <: Expression
    value::Float64
end
@auto_hash_equals_cached struct Variable <: Expression
    name::Symbol
end

# Our transformation function
function xform(@nospecialize(node))
    @match2 node begin
        # identity elements
        Const(-0.0)        => Const(0.0)
        Add(Const(0.0), x) => x
        Add(x, Const(0.0)) => x
        Sub(x, Const(0.0)) => x
        Mul(Const(1.0), x) => x
        Mul(x, Const(1.0)) => x
        Div(x, Const(1.0)) => x
        Mul(Const(0.0) && x, _) => x
        Mul(_, x && Const(0.0)) => x
        # constant folding
        Add(Const(x), Const(y)) => Const(x + y)
        Sub(Const(x), Const(y)) => Const(x - y)
        Neg(Const(x))           => Const(-x)
        Mul(Const(x), Const(y)) => Const(x * y)
        Div(Const(x), Const(y)) => Const(x / y)
        # Algebraic Identities
        Sub(x, x)               => Const(0.0)
        Neg(Neg(x))             => x
        Sub(x, Neg(y))          => Add(x, y)
        Add(x, Neg(y))          => Sub(x, y)
        Add(Neg(x), y)          => Sub(y, x)
        Neg(Sub(x, y))          => Sub(y, x)
        Add(x, x)               => Mul(x, Const(2.0))
        Add(x, Mul(Const(k), x))=> Mul(x, Const(k + 1))
        Add(Mul(Const(k), x), x)=> Mul(x, Const(k + 1))
        # Move constants to the left
        Add(x, k::Const)        => Add(k, x)
        Mul(x, k::Const)        => Mul(k, x)
        # Move negations up the tree
        Sub(Const(0.0), x)      => Neg(x)
        Sub(Neg(x), y)          => Neg(Add(x, y))
        Mul(Neg(x), y)          => Neg(Mul(x, y))
        Mul(x, Neg(y))          => Neg(Mul(x, y))
        x                       => x
    end
end

x = Variable(:x)
y = Variable(:y)
z = Variable(:z)
zero = Const(0.0)
one = Const(1.0)

e1 = Add(zero, x)
e2 = Add(x, zero)
e3 = Sub(x, zero)
e4 = Mul(one, y)
e5 = Mul(y, one)
e6 = Div(z, one)
e7 = Add(Const(3), Const(4))
e8 = Sub(Const(5), Const(6))
e9 = Neg(e7)
e10 = Mul(e8, e9)
e11 = Div(e10, Add(one, one))
e12 = Neg(Neg(e1))
e13 = Sub(e2, Neg(e3))
e14 = Add(e4, Neg(e5))
e15 = Add(Neg(e6), e7)
e16 = Neg(Sub(e8, e9))
e17 = Sub(Neg(e10), e11)
e18 = Add(Neg(e12), Neg(e13))
e19 = Mul(Neg(e14), e15)
e20 = Mul(e16, Neg(e17))
e21 = Sub(Neg(e18), e19)
e22 = Add(e20, Neg(e21))
expr = e22

# The expected results of simplification
expected = Sub(Const(-63.0), Mul(Const(3.0), x))

function simplify(node;
    detect_cycles::Bool = false,
    max_transformations_per_node::Int = 5,
    recursive::Bool = true)
    bottom_up_rewrite(xform, node; detect_cycles, max_transformations_per_node, recursive)
end

@assert simplify(expr) == expected

function f(expr::Expression, n::Int;
    detect_cycles::Bool = false,
    max_transformations_per_node::Int = 5,
    recursive::Bool = true)
    for i in 1:n
        simplify(expr; detect_cycles, max_transformations_per_node, recursive)
    end
end

function performance_test(expr::Expression;
    detect_cycles::Bool = false,
    max_transformations_per_node::Int = 5,
    recursive::Bool = true)
    f(expr, 2; detect_cycles, max_transformations_per_node, recursive) # warm-up
    GC.gc()
    n = 200000
    println("testing $(commas(n)) iterations with detect_cycles = $detect_cycles, max_transformations_per_node = $max_transformations_per_node, recursive = $recursive")
    @time f(expr, n; detect_cycles, max_transformations_per_node, recursive)
    GC.gc()
end

# Insert commas in an integer display every three positions.
# See "Regular Expressions Cookbook," by Goyvaerts and Levithan, O'Reilly, 2nd Ed, p. 402
function commas(num::Integer)
    str = string(num)
    return replace(str, r"(?<=[0-9])(?=(?:[0-9]{3})+(?![0-9]))" => ",")
end

detect_cycles = false
max_transformations_per_node=5
recursive = false

# for detect_cycles in [false, true]
#     for max_transformations_per_node in [0, 5]
        for recursive in [false, true]
            performance_test(expr; detect_cycles, max_transformations_per_node, recursive)
        end
#     end
# end


end
nothing
