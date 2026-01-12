package model.beans;

import java.util.ArrayList;

public class Prodotto {
    private int id, quantitaProdotto;
    private double prezzo, peso;
    private String dimensioni, marca, modello, immagine, descrizione;
    private Categoria categoria;
    private ArrayList<Recensione> recensioni;
    private ArrayList<Specifiche> specifiche;


    public Prodotto() {
        super();
    }

    public ArrayList<Specifiche> getSpecifiche() {
        return specifiche;
    }

    public void setSpecifiche(ArrayList<Specifiche> specifiche) {
        if (specifiche == null) {
            throw new IllegalArgumentException("La lista delle specifiche non può essere null");
        }
        this.specifiche = specifiche;
    }

    public ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    public void setRecensioni(ArrayList<Recensione> recensioni) {
        if (recensioni == null) {
            throw new IllegalArgumentException("La lista delle recensioni non può essere null");
        }
        this.recensioni = recensioni;
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public int getQuantitaProdotto() {
        return quantitaProdotto;
    }

    public void setQuantitaProdotto(int quantitaProdotto) {
        if (quantitaProdotto < 0) {
            throw new IllegalArgumentException("La quantità del prodotto non può essere negativa");
        }
        this.quantitaProdotto = quantitaProdotto;
    }

    public double getPrezzo() {
        return prezzo;
    }

    public void setPrezzo(double prezzo) {
        if (prezzo < 0) {
            throw new IllegalArgumentException("Il prezzo non può essere negativo");
        }
        this.prezzo = prezzo;
    }

    public double getPeso() {
        return peso;
    }

    public void setPeso(double peso) {
        if (peso < 0) {
            throw new IllegalArgumentException("Il peso non può essere negativo");
        }
        this.peso = peso;
    }

    public String getDimensioni() {
        return dimensioni;
    }

    public void setDimensioni(String dimensioni) {
        this.dimensioni = dimensioni;
    }

    public String getMarca() {
        return marca;
    }

    public void setMarca(String marca) {
        if (marca == null || marca.trim().isEmpty()) {
            throw new IllegalArgumentException("La marca non può essere null o vuota");
        }
        this.marca = marca;
    }

    public String getModello() {
        return modello;
    }

    public void setModello(String modello) {
        if (modello == null || modello.trim().isEmpty()) {
            throw new IllegalArgumentException("Il modello non può essere null o vuoto");
        }
        this.modello = modello;
    }

    public String getImmagine() {
        return immagine;
    }

    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    public String getDescrizione() {
        return descrizione;
    }

    public void setDescrizione(String descrizione) {
        if (descrizione == null || descrizione.trim().isEmpty()) {
            throw new IllegalArgumentException("La descrizione non può essere null o vuota");
        }
        this.descrizione = descrizione;
    }

    public Categoria getCategoria() {
        return categoria;
    }

    public void setCategoria(Categoria categoria) {
        if (categoria == null) {
            throw new IllegalArgumentException("La categoria non può essere null");
        }
        this.categoria = categoria;
    }
}
