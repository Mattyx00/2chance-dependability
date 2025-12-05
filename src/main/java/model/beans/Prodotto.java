package model.beans;

import java.util.ArrayList;

public class Prodotto {
    /* @ spec_public @ */
    private int id, quantitaProdotto;
    /* @ spec_public @ */
    private double prezzo, peso;
    /* @ spec_public @ */
    private String dimensioni, marca, modello, immagine, descrizione;
    /* @ spec_public @ */
    private Categoria categoria;
    /* @ spec_public @ */
    private ArrayList<Recensione> recensioni;
    /* @ spec_public @ */
    private ArrayList<Specifiche> specifiche;

    /* @ public invariant prezzo >= 0; @ */
    /* @ public invariant peso >= 0; @ */
    /* @ public invariant quantitaProdotto >= 0; @ */

    public Prodotto() {
        super();
    }

    /* @ ensures \result == specifiche; @ */
    public ArrayList<Specifiche> getSpecifiche() {
        return specifiche;
    }

    /*
     * @
     * 
     * @ requires specifiche != null;
     * 
     * @ ensures this.specifiche == specifiche;
     * 
     * @
     */
    public void setSpecifiche(ArrayList<Specifiche> specifiche) {
        if (specifiche == null) {
            throw new IllegalArgumentException("La lista delle specifiche non può essere null");
        }
        this.specifiche = specifiche;
    }

    /* @ ensures \result == recensioni; @ */
    public ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    /*
     * @
     * 
     * @ requires recensioni != null;
     * 
     * @ ensures this.recensioni == recensioni;
     * 
     * @
     */
    public void setRecensioni(ArrayList<Recensione> recensioni) {
        if (recensioni == null) {
            throw new IllegalArgumentException("La lista delle recensioni non può essere null");
        }
        this.recensioni = recensioni;
    }

    /* @ ensures \result == id; @ */
    public int getId() {
        return id;
    }

    /* @ ensures this.id == id; @ */
    public void setId(int id) {
        this.id = id;
    }

    /* @ ensures \result == quantitaProdotto; @ */
    public int getQuantitaProdotto() {
        return quantitaProdotto;
    }

    /*
     * @
     * 
     * @ requires quantitaProdotto >= 0;
     * 
     * @ ensures this.quantitaProdotto == quantitaProdotto;
     * 
     * @
     */
    public void setQuantitaProdotto(int quantitaProdotto) {
        if (quantitaProdotto < 0) {
            throw new IllegalArgumentException("La quantità del prodotto non può essere negativa");
        }
        this.quantitaProdotto = quantitaProdotto;
    }

    /* @ ensures \result == prezzo; @ */
    public double getPrezzo() {
        return prezzo;
    }

    /*
     * @
     * 
     * @ requires prezzo >= 0;
     * 
     * @ ensures this.prezzo == prezzo;
     * 
     * @
     */
    public void setPrezzo(double prezzo) {
        if (prezzo < 0) {
            throw new IllegalArgumentException("Il prezzo non può essere negativo");
        }
        this.prezzo = prezzo;
    }

    /* @ ensures \result == peso; @ */
    public double getPeso() {
        return peso;
    }

    /*
     * @
     * 
     * @ requires peso >= 0;
     * 
     * @ ensures this.peso == peso;
     * 
     * @
     */
    public void setPeso(double peso) {
        if (peso < 0) {
            throw new IllegalArgumentException("Il peso non può essere negativo");
        }
        this.peso = peso;
    }

    /* @ ensures \result == dimensioni; @ */
    public String getDimensioni() {
        return dimensioni;
    }

    /* @ ensures this.dimensioni == dimensioni; @ */
    public void setDimensioni(String dimensioni) {
        this.dimensioni = dimensioni;
    }

    /* @ ensures \result == marca; @ */
    public String getMarca() {
        return marca;
    }

    /*
     * @
     * 
     * @ requires marca != null && !marca.trim().isEmpty();
     * 
     * @ ensures this.marca == marca;
     * 
     * @
     */
    public void setMarca(String marca) {
        if (marca == null || marca.trim().isEmpty()) {
            throw new IllegalArgumentException("La marca non può essere null o vuota");
        }
        this.marca = marca;
    }

    /* @ ensures \result == modello; @ */
    public String getModello() {
        return modello;
    }

    /*
     * @
     * 
     * @ requires modello != null && !modello.trim().isEmpty();
     * 
     * @ ensures this.modello == modello;
     * 
     * @
     */
    public void setModello(String modello) {
        if (modello == null || modello.trim().isEmpty()) {
            throw new IllegalArgumentException("Il modello non può essere null o vuoto");
        }
        this.modello = modello;
    }

    /* @ ensures \result == immagine; @ */
    public String getImmagine() {
        return immagine;
    }

    /* @ ensures this.immagine == immagine; @ */
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    /* @ ensures \result == descrizione; @ */
    public String getDescrizione() {
        return descrizione;
    }

    /*
     * @
     * 
     * @ requires descrizione != null && !descrizione.trim().isEmpty();
     * 
     * @ ensures this.descrizione == descrizione;
     * 
     * @
     */
    public void setDescrizione(String descrizione) {
        if (descrizione == null || descrizione.trim().isEmpty()) {
            throw new IllegalArgumentException("La descrizione non può essere null o vuota");
        }
        this.descrizione = descrizione;
    }

    /* @ ensures \result == categoria; @ */
    public Categoria getCategoria() {
        return categoria;
    }

    /*
     * @
     * 
     * @ requires categoria != null;
     * 
     * @ ensures this.categoria == categoria;
     * 
     * @
     */
    public void setCategoria(Categoria categoria) {
        if (categoria == null) {
            throw new IllegalArgumentException("La categoria non può essere null");
        }
        this.categoria = categoria;
    }
}
