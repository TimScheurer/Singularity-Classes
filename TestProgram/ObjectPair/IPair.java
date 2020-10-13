package ObjectPair;

public interface IPair {
    
    //@ public instance ghost \locset footprint;
    //@ public instance model Object left;
    //@ public instance model Object right;
    
    //@ public accessible \inv : footprint;
    //@ public accessible left : footprint;
    //@ public accessible right : footprint;

    //@ public instance invariant \subset(\singleton(footprint), footprint);

    /*@ public normal_behaviour
      @ requires \dl_isolated_from(footprint, leftObj);
      @ ensures \new_elems_fresh(footprint);
      @ ensures left == leftObj;
      @ ensures right == \old(right);
      @ assignable footprint;
      @*/
    public void setLeft(Object leftObj);

    /*@ public normal_behaviour
      @ requires \dl_isolated_from(footprint, rightObj);
      @ ensures \new_elems_fresh(footprint);
      @ ensures right == rightObj;
      @ ensures left == \old(left);
      @ assignable footprint;
      @*/
    public void setRight(Object rightObj);

    /*@ public normal_behaviour
      @ ensures \result == left;
      @ ensures \dl_isolated_from(footprint, \result);
      @ assignable \strictly_nothing;
      @ accessible footprint;      
      @*/
    public Object getLeft();

    /*@ public normal_behaviour
      @ ensures \result == right;
      @ ensures \dl_isolated_from(footprint, \result);
      @ assignable \strictly_nothing;
      @ accessible footprint;
      @*/
    public Object getRight();
    
    /*@ public normal_behaviour
      @ ensures \new_elems_fresh(\result.footprint);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static IPair newInstance(Object left, Object right) {
        Pair newInst = new Pair();
        newInst.setLeft(left);
        newInst.setRight(right);
        return newInst;
    }
}