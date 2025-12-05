package model.beans;

public class Categoria {
    /* @ spec_public @ */
    private String nomeCategoria;

    /* @ public invariant nomeCategoria != null && !nomeCategoria.isEmpty(); @ */

    public Categoria() {
    }

    /*
     * @
     * 
     * @ requires nomeCategoria != null && !nomeCategoria.trim().isEmpty();
     * 
     * @ ensures this.nomeCategoria == nomeCategoria;
     * 
     * @
     */
    public Categoria(String nomeCategoria) {
        if (nomeCategoria == null || nomeCategoria.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }

    /* @ ensures \result == nomeCategoria; @ */
    public String getNomeCategoria() {
        return nomeCategoria;
    }

    /*
     * @
     * 
     * @ requires nomeCategoria != null && !nomeCategoria.trim().isEmpty();
     * 
     * @ ensures this.nomeCategoria == nomeCategoria;
     * 
     * @
     */
    public void setNomeCategoria(String nomeCategoria) {
        if (nomeCategoria == null || nomeCategoria.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }
}
