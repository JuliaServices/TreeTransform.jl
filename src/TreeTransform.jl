module TreeTransform

using StaticArrays
using Rematch2: topological_sort

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

    # If positive, the number of transformations per node after which we
    # throw an exception indicating a likely cycle.
    @_const max_transformations_per_node::Int

    # If positive, the number of transformations (total) after which we
    # throw an exception indicating a likely cycle.  To avoid counting the
    # nodes, this is computed only after we have performed 100 transformations.
    max_transformations::Int

    # Number of transformations performed so far.
    transformation_count::Int

    @_const root_node::Any

    # A map from each node to a fixed point for that node.  A node that
    # is a fixed point would also appear in this map, and map to itself.
    @_const fixed_points::IdDict{Any, Any}

    # A helper function for computing fixed points of arrays.
    fixed_point::Function

    function RewriteContext(
        xform::Function,
        detect_cycles::Bool,
        max_transformations_per_node::Int,
        root_node::Any)
        fixed_points = IdDict{Any, Any}()
        let ctx = new(xform, detect_cycles, max_transformations_per_node, 0, 0, root_node, fixed_points);
            ctx.fixed_point = node -> fixed_point(ctx, node, true)
            ctx
        end
    end
end

function enumerate_children end

"""
    bottom_up_rewrite(
        xform::Function,
        data;
        detect_cycles::Bool = false,
        max_transformations::Int = 5,
        recursive::Bool = true)

Given a data structure (`data`) that does not contain cycles, we
apply a given transformation function (`xform`) at every node, and
return a new data structure with all possible transformations
applied.  Note that the result is a data structure in which every
node is a fixed-point of the transformation function provided.

There are two strategies for reaching the fixed-point.  One strategy
is recursive, by postorder traversal; we first find the fixed point
of each child (recursively), and then repeatedly apply transformations
to the parent node until it is a fixed point.  The other strategy is
iterative, by topological sort; we process nodes one by one from
the leaves to the root, and repeatedly apply transformations to each
node until it is a fixed point.  In either case, when the transformation
function produces a new node, we apply the transformation function to
the new node as well using the recursive strategy.  We use a cache so
that once we have computed the fixed point of a node, we do not need
to recompute it.

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
apply, per node, in the original data structure.  You can enable this
by setting `max_transformations_per_node` to a positive integer.  If you set
`max_transformations_per_node` to 3 and the original data structure contained
100 nodes, then we will throw an exception after performing a total
of 300 calls to the transformation function.

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
"""
function bottom_up_rewrite(
    xform::Function,
    data;
    detect_cycles::Bool = false,
    max_transformations_per_node::Int = 5,
    recursive::Bool = true)

    # We use a mutable struct to hold the state of the transformation.
    # This is a bit of a hack (says CoPilot), but it is the easiest way to pass
    # around the state of the transformation without having to pass
    # around a lot of arguments.
    ctx = RewriteContext(xform, detect_cycles, max_transformations_per_node, data)

    if recursive
        _ = fixed_point(ctx, data, true)

    else
        # Use an iterative version to avoid stack overflow.  It is slower due to the
        # need to start with a topological sort.
        # TODO: we should use this as a strategy automatically when we detect deep graphs.
        # TODO: incorporate the topological sort into the code, below, so that we do not
        # have to actually build the resulting topologically sorted list of nodes.

        # Build a work queue as a list of nodes to be transformed.  Since we are
        # doing a bottom-up transformation, we start with the leaves of the graph
        # as determined by a topological_sort of the nodes reachable from the root.
        # That way, when we get to higher levels in the dag, we will have already
        # transformed the children.  However, when new child nodes are built, they
        # will have to be visited again, recursively.  This avoids the most likely
        # source of stack overflow.
        nodes = topological_sort(enumerate_children, Any[data])
        ctx.max_transformations = max_transformations_per_node * length(nodes)
        @assert nodes[1] === data

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
    end

    result = ctx.fixed_points[data]
    result
end

#
# Users may override this to hide fields that should not be considered
# either for transformation or for passing to the constructor.
#
function fieldnames(x::Type{T}) where { T }
    Base.fieldnames(x)
end

# Count the number of nodes reachable from the root node.
function count_reachable_nodes(root::T) where { T }
    counted = Set{Any}()

    # Note that this is recursive.  If that becomes a problem, we can
    # rewrite it iteratively.
    function count(node::T) where { T }
        node in counted && return
        push!(counted, node)
        for child in enumerate_children(node)
            count(child)
        end
    end

    count(root)
    length(counted)
end

# Enumerate the children of the given node.
function enumerate_children(node::T) where { T }
    names = fieldnames(T)
    num_fields = length(names)
    vs = Vector{Any}(undef, num_fields)
    for i in 1:num_fields
        @inbounds v = getfield(node, i)
        @inbounds vs[i] = v
    end

    vs
end

function enumerate_children(node::AbstractVector{T}) where { T }
    node
end

function rebuild_node(ctx::RewriteContext, node::T) where { T }
    names = fieldnames(T)
    num_fields = length(names)

    # Use a static vector to avoid allocations. Since this method is specialized on T, this
    # code compiles into just copying the fields into stack/registers.
    ws = StaticArrays.SizedVector{num_fields,Any}(nothing for i in 1:num_fields)

    # True if all the fields remain `===`.
    all_same = true

    for i in 1:num_fields
        @inbounds v = getfield(node, i)
        w = fixed_point(ctx, v, true)
        all_same &= v === w
        @inbounds ws[i] = w
    end

    if all_same
        return node
    else
        return T(ws...)
    end
end

function rebuild_node(ctx::RewriteContext, node::Expr)
    head = fixed_point(ctx, node.head, true)
    args = fixed_point(ctx, node.args, true)
    if (head === node.head) && (args === node.args)
        return node
    else
        return Expr(node.head, args...)
    end
end

function rebuild_node(ctx::RewriteContext, node::AbstractArray{T}) where { T }
    length(node) == 0 && return node
    rewritten = Base.Broadcast.broadcast(ctx.fixed_point, node)
    for i in eachindex(node)
        @inbounds node[i] !== rewritten[i] && return rewritten
    end
    return node
end

#
# Transform a node by applying a single iteration of the transformation function
#
function xform(ctx::RewriteContext, @nospecialize(data))
    ctx.transformation_count += 1
    if ctx.max_transformations_per_node > 0 && ctx.transformation_count > 100
        if ctx.max_transformations == 0
            # compute the maximum number of transformations
            ctx.max_transformations =
                ctx.max_transformations_per_node * count_reachable_nodes(ctx.root_node)
        end
        if ctx.transformation_count > ctx.max_transformations
            error("Too many ($(ctx.transformation_count)) transformations.  Perhaps there is a cycle in the rewrite rules.")
        end
    end
    result = ctx.xform_fcn(data)
    # println("  [$(ctx.transformation_count)] xform($data) ===> $result")
    result
end

#
# Transform the given node until it and each of its descendants reach a fixed-point.
#
function fixed_point(ctx::RewriteContext, node::T, rebuild::Bool) where { T }
    # if we already know the fixed-point for this node, return it
    if node in keys(ctx.fixed_points)
        return ctx.fixed_points[node]
    end

    # In case children may have been revised, rebuild the node.
    rewritten = rebuild ? rebuild_node(ctx, node) : node

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
            push!(duplicate_set, rewritten2)
        end
        rewritten = rewritten2
    end

    # We should never get here
    error("Internal error in bottom_up_rewrite")
end

end
