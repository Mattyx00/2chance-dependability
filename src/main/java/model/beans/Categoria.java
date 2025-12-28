package model.beans;

public class Categoria {

    /*@ spec_public @*/
    private String nomeCategoria;

    /*@
      @ ensures nomeCategoria == null;
      @*/
    public Categoria() {
    }

    /*@
      @ public normal_behavior
      @   requires nomeCategoria != null && !nomeCategoria.trim().isEmpty();
      @   assignable this.nomeCategoria;
      @   ensures this.nomeCategoria == nomeCategoria;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires nomeCategoria == null || nomeCategoria.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public Categoria(String nomeCategoria) {
        if (nomeCategoria == null || nomeCategoria.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }

    /*@
      @ ensures \result == nomeCategoria;
      @ pure
      @*/
    public String getNomeCategoria() {
        return nomeCategoria;
    }

    /*@
      @ public normal_behavior
      @   requires nomeCategoria != null && !nomeCategoria.trim().isEmpty();
      @   assignable this.nomeCategoria;
      @   ensures this.nomeCategoria == nomeCategoria;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires nomeCategoria == null || nomeCategoria.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setNomeCategoria(String nomeCategoria) {
        if (nomeCategoria == null || nomeCategoria.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }
}