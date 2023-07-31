# Compute a topological ordering of a set of nodes reachable from the given
# roots by the given successor function.
function topological_sort(visit_successors::F, roots::AbstractVector{Any}) where { F <: Function }
    # Compute pred_counts, the number of predecessors of each node
    pred_counts = Dict{Any, Int}()
    counted = Set{Any}()
    to_count = Vector{Any}(roots)
    sizehint!(to_count, length(to_count) + 2047)

    # broken into a separate function to permit specialization on F and N.
    function count(node::N) where { N }
        visit_successors(node) do succ
            push!(to_count, succ)
            pred_counts[succ] = get(pred_counts, succ, 0) + 1
        end
    end

    while !isempty(to_count)
        node = pop!(to_count)
        node in counted && continue
        push!(counted, node)
        get!(pred_counts, node, 0) # make sure every node has a pred count
        count(node)
    end

    # Prepare a ready set of nodes to output that have no predecessors
    ready = Any[]
    for (k, v) in pred_counts
        v == 0 && push!(ready, k)
    end

    result = Any[]
    sizehint!(result, length(pred_counts))

    function decrement_pred_count(@nospecialize(node))
        count = pred_counts[node]
        @assert count > 0
        count -= 1
        pred_counts[node] = count
        count == 0 && push!(ready, node)
    end

    # remove the node by decrementing the predecessor counts of its successors
    function remove_node(node::N) where { N }
        visit_successors(decrement_pred_count, node)
    end

    while !isempty(ready)
        node = pop!(ready)
        push!(result, node)
        remove_node(node)
    end

    # all of the nodes should have been output by now.  Otherwise there was a cycle.
    if length(pred_counts) != length(result)
        error("graph had a cycle involving ", [k for (k, v) in pred_counts if v != 0], ".")
    end

    result
end
