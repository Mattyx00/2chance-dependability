package model.beans;

public class Categoria {

    private /*@ spec_public nullable @*/ String nomeCategoria;

    /*@
      @ ensures nomeCategoria == null;
      @*/
    public Categoria() {
    }

    /*@
      @ requires nomeCategoria != null;
      @ ensures this.nomeCategoria == nomeCategoria;
      @*/
    public Categoria(String nomeCategoria) {
        if (nomeCategoria == null) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        boolean isAllWhitespace = true;
        for (int i = 0; i < nomeCategoria.length(); i++) {
            if (nomeCategoria.charAt(i) > ' ') {
                isAllWhitespace = false;
                break;
            }
        }
        if (isAllWhitespace) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }

    /*@
      @ ensures \result == nomeCategoria;
      @*/
    public /*@ nullable @*/ String getNomeCategoria() {
        return nomeCategoria;
    }

    /*@
      @ requires nomeCategoria != null;
      @ ensures this.nomeCategoria == nomeCategoria;
      @*/
    public void setNomeCategoria(String nomeCategoria) {
        if (nomeCategoria == null) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        boolean isAllWhitespace = true;
        for (int i = 0; i < nomeCategoria.length(); i++) {
            if (nomeCategoria.charAt(i) > ' ') {
                isAllWhitespace = false;
                break;
            }
        }
        if (isAllWhitespace) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }
}