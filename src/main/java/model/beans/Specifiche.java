package model.beans;

public class Specifiche {
    /* @ spec_public @ */
    private String nome, valore;

    /* @ public invariant nome != null && !nome.isEmpty(); @ */
    /* @ public invariant valore != null && !valore.isEmpty(); @ */

    public Specifiche() {
        super();
    }

    /*
     * @
     * 
     * @ requires nome != null && !nome.trim().isEmpty();
     * 
     * @ requires valore != null && !valore.trim().isEmpty();
     * 
     * @ ensures this.nome == nome && this.valore == valore;
     * 
     * @
     */
    public Specifiche(String nome, String valore) {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della specifica non può essere null o vuoto");
        }
        if (valore == null || valore.trim().isEmpty()) {
            throw new IllegalArgumentException("Il valore della specifica non può essere null o vuoto");
        }
        this.nome = nome;
        this.valore = valore;
    }

    /* @ ensures \result == nome; @ */
    public String getNome() {
        return nome;
    }

    /*
     * @
     * 
     * @ requires nome != null && !nome.trim().isEmpty();
     * 
     * @ ensures this.nome == nome;
     * 
     * @
     */
    public void setNome(String nome) {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della specifica non può essere null o vuoto");
        }
        this.nome = nome;
    }

    /* @ ensures \result == valore; @ */
    public String getValore() {
        return valore;
    }

    /*
     * @
     * 
     * @ requires valore != null && !valore.trim().isEmpty();
     * 
     * @ ensures this.valore == valore;
     * 
     * @
     */
    public void setValore(String valore) {
        if (valore == null || valore.trim().isEmpty()) {
            throw new IllegalArgumentException("Il valore della specifica non può essere null o vuoto");
        }
        this.valore = valore;
    }
}
