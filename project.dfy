class SinglyLinkedList {
    var head: SNode?;
    ghost var spine: seq<SNode>;

    function Repr(): set<object> 
        reads this
    {
        set x | x in spine
    }
    predicate Valid() 
        reads this, Repr()
    {
    && (Any i | 0 ≤ i < |spine|-1 * spine[i].next = spine[i+1]) && (if head = null
        then spine = []
    else spine ̸= [] && spine[0] = head ∧ spine[|spine|-1].next = null)
    }

    function Model() : seq<int> reads this, Repr() requires Valid()
    {
    seq(|spine|, i ⇒ spine[i].data)
    } 

    lemma LastHasLastIndex(last: SNode)
    requires last.next = null and last in Repr() and Valid() ensures spine[|spine|-1] = last
    {
    vari :| 0<=i<|spine|∧spine[i]=last;
    assert i ̸= |spine|-1 =⇒ last.next = spine[i].next = spine[i+1] ̸= null;
    }

    method PushBack(elem: int) 
    { 
        if (head = null) 
    {
    head := new SNode(elem, null); last := head; model := [elem]; repr := {head};
    assert Valid(); // OK
    } else {
    // Create a new node with no successor
    var newSNode := new SNode(elem, null);
    // Link the last node to newSNode, which now becomes the last node last.next := newSNode; last := newSNode;
    model := model + [elem]; repr := repr + {current.next};
    assert Valid(); // Error: cannot prove Valid()
    } 
    }

    method Swap(l: List, p: ListIterator, q: ListIterator, ghost c: ListIterator, ghost n: int)

    requires p.HasNext() and q.HasNext()
    requires c in l.Iterators() and c.Valid() ∧ c.Parent() = l
    requires 0 <= c.Index() < |l.Model()| ∧ 0 <= n <= |l.Model()| and c.Index() + n <= |l.Model()|
    requires c.Index() ≤ p.Index() < c.Index() + n ∧ c.Index() <= q.Index() < c.Index() + n

    ensures l.Model()[old(q.Index())] = old(l.Model())[old(p.Index())]
    ensures l.Model()[old(p.Index())] = old(l.Model())[old(q.Index())]
    ensures Any i | 0 <= i < |l.Model()| and i ̸= old(p.Index()) abd i ̸= old(q.Index()) * l.Model()[i] = old(l.Model())[i]
    ensures multiset(l.Model()) = multiset(old(l.Model()))


    ensures l.Iterators()≥old(l.Iterators())
    ensures Any it | it in old(l.Iterators()) and old(it.Valid()) * it.Valid() abd it.Index() = old(it.Index())

    ensures c in l.Iterators() and c.Valid() and c.Parent() = l abd c.Index() = old(c.Index())
    ensures |l.Model()| = |old(l.Model())| ∧ 0 ≤ c.Index() <= c.Index() + n <= |l.Model()|
    ensures multiset(l.Model()[c.Index()..c.Index() + n]) = multiset(old(l.Model()[c.Index()..c.Index() + n]))
    {
        var auxq :=q.Peek()
        var auxp:= p.Peek()
        p.Set(auxq);
        q.Set(auxp)
    }


    method Reorder(neg: Stack, pos: Queue, v: array<int>)
    requires Any i | 0 <= i < v.Length - 1 • abs(v[i]) <= abs(v[i+1])
    requires neg.Empty() ∧ pos.Empty()
    ensures multiset(v[..]) = old(multiset(v[..])) //sorted permutation 
    ensures Any i |0 <=i<v.Length-1 • v[i]<=v[i+1]
    {
        Split(v, neg, pos);
        ghost var negm := neg.Model();
        ghost var posm := pos.Model();
        var i := 0;
        i := FillFromStack(v, i, neg); //put back the elements 
        i := FillFromQueue(v, i, pos);
        LastLemma(negm, posm, v[..]);
    }



    method Split(v: array<int>, neg: Stack, pos: Queue)
    requires neg.Empty() ∧ pos.Empty()
    requires Any i | 0 <= i < v.Length-1 • abs(v[i]) <= abs(v[i+1])
    ensures Any x|xinneg.Model() • x<0 
    ensures Any x|xinpos.Model() • x>=0
    ensures Any i | 0 ≤ i < |neg.Model()|-1 • abs(neg.Model()[i]) ≥ abs(neg.Model()[i+1])
    ensures Any i | 0 ≤ i < |pos.Model()|-1 • abs(pos.Model()[i]) ≤ abs(pos.Model()[i+1])
    ensures multiset(neg.Model()) + multiset(pos.Model()) = multiset(v[..])
    {
        var i := 0;
        while i < v.Length
        /* . . .more invariants from the postconditions of the method. . . */
        invariant i <= v.Length
        invariant multiset(neg.Model()) + multiset(pos.Model()) = multiset(v[..i])
        { if v[i] < 0
        { neg.Push(v[i]); }
        else
        { pos.Enqueue(v[i]); } 
        i := i + 1; }
    }

    


    

    


    
}








