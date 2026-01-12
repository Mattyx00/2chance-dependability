package model.beans;

public class Categoria {

    private String nomeCategoria;

    public Categoria() {
    }

    public Categoria(String nomeCategoria) {
        if (nomeCategoria == null || nomeCategoria.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }

    public String getNomeCategoria() {
        return nomeCategoria;
    }

    public void setNomeCategoria(String nomeCategoria) {
        if (nomeCategoria == null || nomeCategoria.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto");
        }
        this.nomeCategoria = nomeCategoria;
    }
}