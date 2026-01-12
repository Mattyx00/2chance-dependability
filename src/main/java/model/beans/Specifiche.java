package model.beans;

public class Specifiche {

    private String nome, valore;

    public Specifiche() {
        super();
    }

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

    public String getNome() {
        return nome;
    }

    public void setNome(String nome) {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della specifica non può essere null o vuoto");
        }
        this.nome = nome;
    }

    public String getValore() {
        return valore;
    }

    public void setValore(String valore) {
        if (valore == null || valore.trim().isEmpty()) {
            throw new IllegalArgumentException("Il valore della specifica non può essere null o vuoto");
        }
        this.valore = valore;
    }
}
