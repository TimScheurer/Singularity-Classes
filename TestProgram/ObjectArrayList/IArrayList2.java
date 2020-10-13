package ObjectArrayList;

public interface IArrayList2 {
    
    //@ public ghost instance \bigint footprint;
    //@ public model instance \seq theList;
    //@ public accessible \inv : footprint;

    /*@ public normal_behaviour
      @ requires theList.length < 16;
      @ requires obj != null;
      @ ensures theList == \seq_concat(\old(theList), \seq_singleton(obj));
      @ assignable footprint;
      @*/
    public void insert(Object obj);

    /*@ public normal_behaviour
      @ requires 0 <= index && index < theList.length;
      @ ensures \result == (Object)theList[index];
      @ ensures \result != null;
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
      @ assignable \nothing;
      @*/
      public static IArrayList2 newInstance() {
        return new ArrayList2();
    }
}