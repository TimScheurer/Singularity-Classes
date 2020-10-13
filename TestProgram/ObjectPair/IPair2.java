package ObjectPair;

public interface IPair2 {
    
    //@ public instance ghost \bigint footprint;
    //@ public instance model Object left;
    //@ public instance model Object right;
    
    //@ public accessible \inv : footprint;
    //@ public accessible left : footprint;
    //@ public accessible right : footprint;

    /*@ public normal_behaviour
      @ ensures left == leftObj;
      @ ensures right == \old(right);
      @ assignable footprint;
      @*/
    public void setLeft(Object leftObj);

    /*@ public normal_behaviour
      @ ensures right == rightObj;
      @ ensures left == \old(left);
      @ assignable footprint;
      @*/
    public void setRight(Object rightObj);

    /*@ public normal_behaviour
      @ ensures \result == left;
      @ assignable \strictly_nothing;
      @ accessible footprint;      
      @*/
    public Object getLeft();

    /*@ public normal_behaviour
      @ ensures \result == right;
      @ assignable \strictly_nothing;
      @ accessible footprint;
      @*/
    public Object getRight();
    
    /*@ public normal_behaviour
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static IPair2 newInstance(Object left, Object right) {
        Pair newInst = new Pair2();
        newInst.setLeft(left);
        newInst.setRight(right);
        return newInst;
    }
}