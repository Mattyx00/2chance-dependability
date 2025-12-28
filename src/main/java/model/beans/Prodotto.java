package model.beans;

import java.util.ArrayList;

public class Prodotto {
    /*@ spec_public @*/
    private int id, quantitaProdotto;
    /*@ spec_public @*/
    private double prezzo, peso;
    /*@ spec_public nullable @*/
    private String dimensioni, marca, modello, immagine, descrizione;
    /*@ spec_public nullable @*/
    private Categoria categoria;
    /*@ spec_public nullable @*/
    private ArrayList<Recensione> recensioni;
    /*@ spec_public nullable @*/
    private ArrayList<Specifiche> specifiche;

    /*@ public invariant prezzo >= 0; @*/
    /*@ public invariant peso >= 0; @*/
    /*@ public invariant quantitaProdotto >= 0; @*/

    public Prodotto() {
        super();
    }

    /*@ 
      @ ensures \result == specifiche; 
      @ pure
      @*/
    public ArrayList<Specifiche> getSpecifiche() {
        return specifiche;
    }

    /*@
      @ public normal_behavior
      @   requires specifiche != null;
      @   assignable this.specifiche;
      @   ensures this.specifiche == specifiche;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires specifiche == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setSpecifiche(ArrayList<Specifiche> specifiche) {
        if (specifiche == null) {
            throw new IllegalArgumentException("La lista delle specifiche non può essere null");
        }
        this.specifiche = specifiche;
    }

    /*@ 
      @ ensures \result == recensioni; 
      @ pure
      @*/
    public ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    /*@
      @ public normal_behavior
      @   requires recensioni != null;
      @   assignable this.recensioni;
      @   ensures this.recensioni == recensioni;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires recensioni == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setRecensioni(ArrayList<Recensione> recensioni) {
        if (recensioni == null) {
            throw new IllegalArgumentException("La lista delle recensioni non può essere null");
        }
        this.recensioni = recensioni;
    }

    /*@ 
      @ ensures \result == id; 
      @ pure
      @*/
    public int getId() {
        return id;
    }

    /*@
      @ requires true;
      @ assignable this.id;
      @ ensures this.id == id;
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ 
      @ ensures \result == quantitaProdotto; 
      @ pure
      @*/
    public int getQuantitaProdotto() {
        return quantitaProdotto;
    }

    /*@
      @ public normal_behavior
      @   requires quantitaProdotto >= 0;
      @   assignable this.quantitaProdotto;
      @   ensures this.quantitaProdotto == quantitaProdotto;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires quantitaProdotto < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setQuantitaProdotto(int quantitaProdotto) {
        if (quantitaProdotto < 0) {
            throw new IllegalArgumentException("La quantità del prodotto non può essere negativa");
        }
        this.quantitaProdotto = quantitaProdotto;
    }

    /*@ 
      @ ensures \result == prezzo; 
      @ pure
      @*/
    public double getPrezzo() {
        return prezzo;
    }

    /*@
      @ public normal_behavior
      @   requires prezzo >= 0;
      @   assignable this.prezzo;
      @   ensures this.prezzo == prezzo;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires prezzo < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setPrezzo(double prezzo) {
        if (prezzo < 0) {
            throw new IllegalArgumentException("Il prezzo non può essere negativo");
        }
        this.prezzo = prezzo;
    }

    /*@ 
      @ ensures \result == peso; 
      @ pure
      @*/
    public double getPeso() {
        return peso;
    }

    /*@
      @ public normal_behavior
      @   requires peso >= 0;
      @   assignable this.peso;
      @   ensures this.peso == peso;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires peso < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setPeso(double peso) {
        if (peso < 0) {
            throw new IllegalArgumentException("Il peso non può essere negativo");
        }
        this.peso = peso;
    }

    /*@ 
      @ ensures \result == dimensioni; 
      @ pure
      @*/
    public String getDimensioni() {
        return dimensioni;
    }

    /*@
      @ requires true;
      @ assignable this.dimensioni;
      @ ensures this.dimensioni == dimensioni;
      @*/
    public void setDimensioni(String dimensioni) {
        this.dimensioni = dimensioni;
    }

    /*@ 
      @ ensures \result == marca; 
      @ pure
      @*/
    public String getMarca() {
        return marca;
    }

    /*@
      @ public normal_behavior
      @   requires marca != null && !marca.trim().isEmpty();
      @   assignable this.marca;
      @   ensures this.marca == marca;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires marca == null || marca.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setMarca(String marca) {
        if (marca == null || marca.trim().isEmpty()) {
            throw new IllegalArgumentException("La marca non può essere null o vuota");
        }
        this.marca = marca;
    }

    /*@ 
      @ ensures \result == modello; 
      @ pure
      @*/
    public String getModello() {
        return modello;
    }

    /*@
      @ public normal_behavior
      @   requires modello != null && !modello.trim().isEmpty();
      @   assignable this.modello;
      @   ensures this.modello == modello;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires modello == null || modello.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setModello(String modello) {
        if (modello == null || modello.trim().isEmpty()) {
            throw new IllegalArgumentException("Il modello non può essere null o vuoto");
        }
        this.modello = modello;
    }

    /*@ 
      @ ensures \result == immagine; 
      @ pure
      @*/
    public String getImmagine() {
        return immagine;
    }

    /*@
      @ requires true;
      @ assignable this.immagine;
      @ ensures this.immagine == immagine;
      @*/
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    /*@ 
      @ ensures \result == descrizione; 
      @ pure
      @*/
    public String getDescrizione() {
        return descrizione;
    }

    /*@
      @ public normal_behavior
      @   requires descrizione != null && !descrizione.trim().isEmpty();
      @   assignable this.descrizione;
      @   ensures this.descrizione == descrizione;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires descrizione == null || descrizione.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setDescrizione(String descrizione) {
        if (descrizione == null || descrizione.trim().isEmpty()) {
            throw new IllegalArgumentException("La descrizione non può essere null o vuota");
        }
        this.descrizione = descrizione;
    }

    /*@ 
      @ ensures \result == categoria; 
      @ pure
      @*/
    public Categoria getCategoria() {
        return categoria;
    }

    /*@
      @ public normal_behavior
      @   requires categoria != null;
      @   assignable this.categoria;
      @   ensures this.categoria == categoria;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires categoria == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setCategoria(Categoria categoria) {
        if (categoria == null) {
            throw new IllegalArgumentException("La categoria non può essere null");
        }
        this.categoria = categoria;
    }
}
