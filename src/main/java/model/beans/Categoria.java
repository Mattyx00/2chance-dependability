package model.beans;

public class Categoria {
    /* @ spec_public @ */
    private String nomeCategoria;

    public Categoria() {
    }

    /*
     * @
     * 
     * @ ensures \result == nomeCategoria;
     * 
     * @
     */
    public String getNomeCategoria() {
        return nomeCategoria;
    }

    /*
     * @
     * 
     * @ ensures this.nomeCategoria == nomeCategoria;
     * 
     * @
     */
    public void setNomeCategoria(String nomeCategoria) {
        this.nomeCategoria = nomeCategoria;
    }
}
