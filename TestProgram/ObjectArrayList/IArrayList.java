package ObjectArrayList;

public interface IArrayList {

    //@ public ghost instance \locset footprint;
    //@ public model instance \seq theList;
    //@ public accessible \inv : footprint;
    //@ public accessible theList : footprint;

    /*@ public normal_behaviour
      @ requires theList.length < 16;
      @ requires \dl_isolated_from(footprint, obj);
      @ requires obj != null;
      @ ensures \new_elems_fresh(footprint);
      @ ensures theList == \seq_concat(\old(theList), \seq_singleton(obj));
      @ assignable footprint;
      @*/
    public void insert(Object obj);

    /*@ public normal_behaviour
      @ requires 0 <= index && index < theList.length;
      @ ensures \result == (Object)theList[index];
      @ ensures \result != null;
      @ ensures \dl_isolated_from(footprint,\result);
      @ assignable \strictly_nothing;
      @ accessible footprint;
      @*/
    public Object get(int index);

    /*@ public normal_behaviour
      @ ensures \result == theList.length;
      @ assignable \strictly_nothing;
      @ accessible footprint;
      @*/
    public int size();

    /*@ public normal_behaviour
      @ ensures \fresh(\result);
      @ ensures \new_elems_fresh(\result.footprint);
      @ assignable \nothing;
      @*/
      public static IArrayList newInstance() {
        return new ArrayList();
    }
}