package ObjectPair;

public interface IPairClient {
    
    /*@ public normal_behaviour
      @ requires pair1 != pair2;
      @ requires pair1.getLeft() != null;
      @ requires \invariant_for(pair2);
      @ ensures \old(pair1).getLeft() == pair1.getLeft();
      @*/
    public void setFirst(IPair pair1, IPair pair2);
    
    /*@ public normal_behaviour
      @ requires \invariant_for(pair);
      @ requires pair.left != null && pair.right != null;
      @ ensures pair.right == \old(pair.left);
      @ ensures pair.left == \old(pair.right);
      @*/
      public void swap(IPair pair);
}