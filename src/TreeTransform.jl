module TreeTransform

using Rematch2: topological_sort, ImmutableVector

export bottom_up_rewrite

# const fields only suppored >= Julia 1.8
macro _const(x)
    if VERSION >= v"1.8"
        Expr(:const, esc(x))
    else
        esc(x)
    end
end

dropfirst(a) = a[2:length(a)]

# temporarily disable assertions in the implementation.
macro devassert(x...)
    # esc(:(@assert($(x...))))
    nothing
end

# The state of the transformation is maintained in an instance of this struct.
mutable struct RewriteContext
    # The user's transformation function.
    @_const xform_fcn::Function

    # If true, we are detecting cycles of the first kind.
    @_const detect_cycles::Bool

    # If positive, the number of individual node transformations before we
    # throw an exception indicating a likely cycle.
    remaining_transformations::Int

    # A map from each node to a fixed point for that node.  A node that
    # is a fixed point would also appear in this map, and map to itself.
    @_const fixed_points::IdDict{Any, Any}

    function RewriteContext(
        xform::Function,
        detect_cycles::Bool,
        max_transformations::Int)
        fixed_points = IdDict{Any, Any}()
        new(xform, detect_cycles, max_transformations, fixed_points);
    end
end

"""
    bottom_up_rewrite(
        xform::Function,
        data;
        detect_cycles::Bool = false,
        max_transformations::Int = 0)

Given a data structure (`data`) that does not contain cycles, we
apply a given transformation function (`xform`) at every node, and
return a new data structure with all possible transformations
applied.  Note that the result is a data structure in which every
node is a fixed-point of the transformation function provided.

By default, we do not detect cycles in the applied transformations.
There are two kinds of cycles that can occur: first, if some sequence
of transformations result in the same data structure.  Second, if
the transformation function produces additional nodes that were not
in the previous data structure, and additional rules apply to the
new nodes.

We offer two mechanisms to detect cycles.  First, we can detect the
simple cycles of the first kind automatically, but at additional
cost.  You can enable this by setting `detect_cycles` to `true`.
Second, you can give a limit on the number of transformations to
apply per node in the original data structure.  You can enable this
by setting `max_transformations` to a positive integer.  For example,
you set `max_transformations` to 3 and the original data structure
contained 100 nodes, then we will only apply 300 distinct non-identity
node transformations anywhere in the graph before throwing an
exception.

The `transform` function should take a single argument, the node
to transform, and return a transformed version of that node.  The
`transform` function should not modify the original node.  If no
transformation applies to a node, then the `transform` function
should return the original node.

The nodes of the data structure can be of arbitrary Julia struct
types, but the data structure as a whole must be a directed acyclic
graph, i.e., it must not contain cycles.  The implementation examines
the set of constructors of the nodes, and the set of fields that
correspond to the parameters of each constructor.  We only consider
constructors that are not vararg, have no keyword arguments, and
whose parameter names all correspond to fields of the node type.
We take the constructor(s) with the longest parameter list with
these properties.  We throw an exception if there are more than one
and they name different fields or in different orders. Finally, we
use such a unique order to determine the children nodes to which
we will apply the transformation function.  That constructor will
be called to rewrite the parent node if any transformed child is
different from the original child.

The implementation keeps track of which nodes have reached a
fixed-point, so that we can perform the minimum number of
transformations.  We also keep track of the number of transformations
applied to each node, so that we can detect cycles of the second
kind.

This facility is less general than the E-graph approach, but it is
(hopefully) more efficient and easier to use when it applies.  The
E-graph approach can handle cycles, but it is more expensive and
requires more work to set up. See also "Metatheory.jl: Fast and
Elegant Algebraic Computation in Julia with Extensible Equality
Saturation" by Alessandro Cheli, 2021, <https://arxiv.org/abs/2102.07888>

You can specialize the behavior for some nodes, e.g. to force child
nodes to be visited in a particular order.  For example, if you
have a node that represents the conjunction of two boolean expressions,
you might want to force the left child to be visited before the
right child, and then if the left child is `false`, you can skip
the right child.  You can also use this to skip rewriting of certain
child nodes.  **The way to do this is not yet defined.**
"""
function bottom_up_rewrite(
    xform::Function,
    data;
    detect_cycles::Bool = false,
    max_transformations::Int = 0
)

    # Build a work queue as a list of nodes to be transformed.  Since we are
    # doing a bottom-up transformation, we start with the leaves of the graph
    # as determined by a topological_sort of the nodes reachable from the root.
    # That way, when we get to higher levels in the dag, we will have already
    # transformed the children.  However, when new child nodes are built, they
    # will have to be visited again.
    nodes = topological_sort(enumerate_children, Any[data])
    @assert nodes[1] === data

    # We use a mutable struct to hold the state of the transformation.
    # This is a bit of a hack (says CoPilot), but it is the easiest way to pass
    # around the state of the transformation without having to pass
    # around a lot of arguments.
    ctx = RewriteContext(xform, detect_cycles, max_transformations * length(nodes))

    # Transform each node until it reaches a fixed-point.
    any_changes = false
    for node in reverse(nodes)
        # println("processing node ($(objectid(node))) $node")
        newnode = fixed_point(ctx, node, any_changes)
        if newnode !== node
            any_changes = true
        end
        @devassert node in keys(ctx.fixed_points)
        @devassert newnode in keys(ctx.fixed_points)
    end
    # transformed = fixed_point(ctx, data, true)

    result = ctx.fixed_points[data]
    result
end

function enumerate_children_names(node_type::Type{T}) where { T }
    # We only consider constructors that are not vararg, have no keyword arguments,
    # and whose parameter names all correspond to fields of the node type.
    # We take the constructor(s) with the longest parameter list with these properties.
    # We throw an exception if there are more than one and they name different fields
    # or in different orders.

    members = fieldnames(node_type)
    length(members) == 0 && return members

    # Search for constructor methods that have no keyword parameters, and are not varargs.
    meths = Method[methods(node_type)...]
    meths = filter(m -> !m.isva && length(Base.kwarg_decl(m))==0, meths)
    # drop the implicit var"#self#" argument
    argnames_list = map(m -> dropfirst(Base.method_argnames(m)), meths)
    # narrow to arg lists where all parameter names correspond to members
    argnames_list = unique(filter(l -> all(n -> n in members, l), argnames_list))
    # find the longest such arg list
    isempty(argnames_list) && return Symbol[]
    len = maximum(map(length, argnames_list))
    argnames_list = filter(l -> length(l) == len, argnames_list)

    if length(argnames_list) == 1
        # found a uniquely satisfying order for member names
        return only(argnames_list)
    elseif len == length(members)
        # no unique constructor, but the correct number of fields exist; use them
        return vcat(members)
    else
        # no unique constructor, and not all fields are used.  Throw an error when
        # a node is encountered.
        return :(error("Cannot infer an order in which to construct the children of $(node_type)."))
    end
end

@generated function enumerate_children(node::T) where { T }
    # Since this is a @generated function, node is actually the type of the argument.
    node_type = node
    member_names = enumerate_children_names(node_type)
    length(member_names) == 0 && return ImmutableVector{Any}([])
    :(Any[$((:(node.$m) for m in member_names)...)])
end

# A non-generated version of enumerate_children for debugging
# function enumerate_children(node::T) where { T }
#     node_type = typeof(node)
#     member_names = enumerate_children_names(node_type)
#     Any[getfield(node, m) for m in member_names]
# end

# Rebuild the node with revised children, if any
# If no children have changed, then return the original node.
# A prerequisite to calling this function is that all children must
# have had their fixed-point value recorded in ctx.fixed_points.
@generated function rebuild_node(ctx::RewriteContext, node::T) where { T }
    # Generate type-specific code to rebuild the node in case children have changed.

    # Note: since this is a @generated function, node is actually the type of the node.
    node_type = node
    member_names = enumerate_children_names(node)
    length(member_names) == 0 && return :node

    result_expression = Expr(:block)
    code = result_expression.args

    # Cache the fields and their translations in local variables.
    cached_translations = map(m -> Symbol(m, "'"), member_names)
    for (m, t) in zip(member_names, cached_translations)
        push!(code, quote
            local $m = node.$m
            # local $t = ctx.fixed_points[$m]
            local $t = $fixed_point(ctx, $m, $(true))
        end)
    end
    # println("code so far: $result_expression")
    # Determine if any have changed and, if so, reconstruct.
    any_changed = mapreduce(
        ((m, t),) -> :($m !== $t), (a,b) -> :($a || $b), zip(member_names, cached_translations))
    # println("any_changed: $any_changed")
    rebuild = :($node_type($(cached_translations...)))
    # println("rebuild: $rebuild")
    push!(code, quote
        if $any_changed
            $rebuild
        else
            node
        end
    end)
    # println("rebuild_node(ctx, node::$node_type) = $result_expression")
    result_expression
end

# A non-generated version of rebuild_node for debugging
# function rebuild_node(ctx::RewriteContext, node::T) where { T }
#     node_type = typeof(node)
#     fields = enumerate_children(node)
#     length(fields) == 0 && return node
#     cached_translations = Any[ctx.fixed_points[m] for m in fields]
#     any_changed = any(map((m,t) -> m !== t, fields, cached_translations))
#     return any_changed ? node_type(cached_translations...) : node
# end

# Transform a node by applying a single iteration of the transformation function
function xform(ctx::RewriteContext, @nospecialize(data))
    if ctx.remaining_transformations > 0 && (ctx.remaining_transformations -= 1) == 0
        error("Too many transformations.  Perhaps there is an expansionary cycle in the rewrite rules.")
    end
    ctx.xform_fcn(data)
end

#
# Transform the given node until it and each of its descendants reach a fixed-point.
#
function fixed_point(ctx::RewriteContext, node::T, rebuild::Bool) where { T }
    # if we already know the fixed-point for this node, return it
    if node in keys(ctx.fixed_points)
        return ctx.fixed_points[node]
    end

    rebuild = true
    rewritten = node
    if rebuild
        # In case children may have been revised, rebuild the node.
        rewritten = rebuild_node(ctx, node)
        # println("  rebuilt to ($(objectid(rewritten))) $rewritten")
        @devassert all(child in keys(ctx.fixed_points) for child in enumerate_children(rewritten))
    end

    if ctx.detect_cycles
        # Prepare a dupicate-detection set, if needed to detect non-expansionary
        # cycles in the transformation.
        duplicate_set = Set{Any}()
    end

    # Continue transforming until we reach a fixed-point for this node
    while true
        # Apply a single transformation to the node, and then recursively transform
        # any new children to a fixed-point.  We don't apply further transformations
        # to the top-level node recursively because we want to avoid unnecessarily
        # deep recursion.  Instead we do it this loop.
        rewritten2 = xform(ctx, rewritten)
        if rewritten2 === rewritten
            ctx.fixed_points[node] = rewritten
            ctx.fixed_points[rewritten] = rewritten
            # println("  rewritten to ($(objectid(rewritten))) $rewritten")
            return rewritten
        end
        rewritten2 = rebuild_node(ctx, rewritten2)
        if ctx.detect_cycles
            if rewritten2 in duplicate_set
                error("Cycle detected in bottom_up_rewrite")
            end
            duplicate_set.add(rewritten2)
        end
        rewritten = rewritten2
    end

    # We should never get here
    error("Internal error in bottom_up_rewrite")
end

end
