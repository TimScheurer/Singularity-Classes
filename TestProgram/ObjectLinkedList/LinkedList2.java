package ObjectLinkedList;

public class LinkedList2 implements ILinkedList {
   
    //@ private represents theList = val != null ? (next != null ? \seq_concat(\seq_singleton(val), next.theList) : \seq_singleton(val)) : \seq_empty;
    //@ private invariant footprint == ((next == null) ? \all_fields(this) : \set_union(\all_fields(this), next.footprint));
    //@ private invariant next != null ==> \invariant_for(next);
    //@ private invariant next != null ==> val != null;
    //@ private invariant val != null ==> \dl_isolated_from(footprint, val); 
 
    private ILinkedList2 /*@ nullable */ next;
    private Object /*@ nullable */ val;

    public LinkedList2() {
        //@ set footprint = \all_fields(this);
    }

    public void insert(Object obj) {
        if (val == null) {
            val = obj;
            return;
        } else if (next != null) {
            {
                next.insert(obj);
            }
        } else {
            next = ILinkedList2.newInstance();
            //@ set footprint = \set_union(\all_fields(this), \singleton(next.footprint));
            next.insert(obj);
        }
    }

    public Object get(int index) {
        if (index == 0) return val;

        return next.get(index - 1);
    }

    public int size() {
        if (next != null) return next.size() + 1;
        if (val != null) return 1;
        return 0;
    }
}