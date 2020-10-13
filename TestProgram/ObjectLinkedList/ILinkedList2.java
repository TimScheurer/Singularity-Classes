package ObjectLinkedList;

public interface ILinkedList2 {
        

    //@ public ghost instance \bigint footprint;
    //@ public model instance \seq theList;
    //@ public accessible theList : footprint;
    //@ public accessible \inv : footprint;
  
    //@ public instance invariant (\forall int i; 0 <= i &&  i < theList.length; theList[i] instanceof Object);
  
    /*@ public normal_behaviour
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
      @*/
    public int size();
    
    /*@ public normal_behaviour
      @ ensures \fresh(\result);
      @ ensures \result.theList == \seq_empty;
      @ ensures \invariant_for(\result);
      @ ensures \result != null;
      @ assignable \nothing;
      @*/
    public static ILinkedList2 newInstance() {
        return new LinkedList();
    }
}