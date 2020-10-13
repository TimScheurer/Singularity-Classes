package ObjectLinkedList;

public interface ILinkedList {
 
    //@ public ghost instance \locset footprint;
    //@ public model instance \seq theList;
    //@ public accessible theList : footprint;
    //@ public accessible \inv : footprint;

    //@ public instance invariant (\forall int i; 0 <= i &&  i < theList.length; theList[i] instanceof Object);
    //@ public instance invariant \subset(\singleton(footprint), footprint);

    /*@ public normal_behaviour
      @ requires obj != null;
      @ requires \dl_isolated_from(footprint, obj);
      @ ensures \new_elems_fresh(footprint);
      @ ensures theList == \seq_concat(\old(theList), \seq_singleton(obj));
      @ assignable footprint;
      @*/
    public void insert(Object obj);

    /*@ public normal_behaviour
      @ requires 0 <= index && index < theList.length;
      @ ensures \dl_isolated_from(footprint, \result);
      @ ensures \result == (Object)theList[index];
      @ ensures \result != null;
      @ measured_by index;
      @ assignable \strictly_nothing;
      @ accessible footprint;
      @*/
    public Object get(int index);

    /*@ public normal_behaviour
      @ ensures \result == theList.length;
      @ assignable \strictly_nothing;
      @*/
    public int size();
    
    /*@ public normal_behaviour
      @ ensures \fresh(\result);
      @ ensures \result.theList == \seq_empty;
      @ ensures \result != null;
      @ ensures \new_elems_fresh(\result.footprint);
      @ assignable \nothing;
      @*/
    public static ILinkedList newInstance() {
        return new LinkedList();
    }
}