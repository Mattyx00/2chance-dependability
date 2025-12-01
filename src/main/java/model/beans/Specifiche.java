package model.beans;

public class Specifiche {
    /* @ spec_public @ */
    private String nome, valore;

    public Specifiche() {
        super();
    }

    /* @ ensures \result == nome; @ */
    public String getNome() {
        return nome;
    }

    /* @ ensures this.nome == nome; @ */
    public void setNome(String nome) {
        this.nome = nome;
    }

    /* @ ensures \result == valore; @ */
    public String getValore() {
        return valore;
    }

    /* @ ensures this.valore == valore; @ */
    public void setValore(String valore) {
        this.valore = valore;
    }
}
