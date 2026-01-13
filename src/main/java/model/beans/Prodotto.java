package model.beans;

import java.util.ArrayList;

public class Prodotto {
    /*@ spec_public @*/ private int id;
    /*@ spec_public @*/ private int quantitaProdotto;
    /*@ spec_public @*/ private double prezzo;
    /*@ spec_public @*/ private double peso;
    /*@ spec_public nullable @*/ private String dimensioni;
    /*@ spec_public nullable @*/ private String marca;
    /*@ spec_public nullable @*/ private String modello;
    /*@ spec_public nullable @*/ private String immagine;
    /*@ spec_public nullable @*/ private String descrizione;
    /*@ spec_public nullable @*/ private Categoria categoria;
    /*@ spec_public nullable @*/ private ArrayList<Recensione> recensioni;
    /*@ spec_public nullable @*/ private ArrayList<Specifiche> specifiche;

    /*@ public invariant quantitaProdotto >= 0; @*/
    /*@ public invariant prezzo >= 0; @*/
    /*@ public invariant peso >= 0; @*/

    public Prodotto() {
        super();
    }

    /*@ 
      @ ensures \result == specifiche; 
      @*/
    public /*@ pure nullable @*/ ArrayList<Specifiche> getSpecifiche() {
        return specifiche;
    }

    /*@ 
      @ ensures this.specifiche == specifiche;

      @*/
    public void setSpecifiche(ArrayList<Specifiche> specifiche) {
        if (specifiche == null) {
            throw new IllegalArgumentException("La lista delle specifiche non può essere null");
        }
        this.specifiche = specifiche;
    }

    /*@ 
      @ ensures \result == recensioni; 
      @*/
    public /*@ pure nullable @*/ ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    /*@ 
      @ ensures this.recensioni == recensioni;

      @*/
    public void setRecensioni(ArrayList<Recensione> recensioni) {
        if (recensioni == null) {
            throw new IllegalArgumentException("La lista delle recensioni non può essere null");
        }
        this.recensioni = recensioni;
    }

    /*@ 
      @ ensures \result == id; 
      @*/
    public /*@ pure @*/ int getId() {
        return id;
    }

    /*@ 
      @ ensures this.id == id; 
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ 
      @ ensures \result == quantitaProdotto; 
      @*/
    public /*@ pure @*/ int getQuantitaProdotto() {
        return quantitaProdotto;
    }

    /*@ 
      @ ensures this.quantitaProdotto == quantitaProdotto;

      @*/
    public void setQuantitaProdotto(int quantitaProdotto) {
        if (quantitaProdotto < 0) {
            throw new IllegalArgumentException("La quantità del prodotto non può essere negativa");
        }
        this.quantitaProdotto = quantitaProdotto;
    }

    /*@ 
      @ ensures \result == prezzo; 
      @*/
    public /*@ pure @*/ double getPrezzo() {
        return prezzo;
    }

    /*@ 
      @ ensures this.prezzo == prezzo;

      @*/
    public void setPrezzo(double prezzo) {
        if (prezzo < 0) {
            throw new IllegalArgumentException("Il prezzo non può essere negativo");
        }
        this.prezzo = prezzo;
    }

    /*@ 
      @ ensures \result == peso; 
      @*/
    public /*@ pure @*/ double getPeso() {
        return peso;
    }

    /*@ 
      @ ensures this.peso == peso;

      @*/
    public void setPeso(double peso) {
        if (peso < 0) {
            throw new IllegalArgumentException("Il peso non può essere negativo");
        }
        this.peso = peso;
    }

    /*@ 
      @ ensures \result == dimensioni; 
      @*/
    public /*@ pure nullable @*/ String getDimensioni() {
        return dimensioni;
    }

    /*@ 
      @ ensures this.dimensioni == dimensioni; 
      @*/
    public void setDimensioni(String dimensioni) {
        this.dimensioni = dimensioni;
    }

    /*@ 
      @ ensures \result == marca; 
      @*/
    public /*@ pure nullable @*/ String getMarca() {
        return marca;
    }

    /*@ 
      @ ensures this.marca == marca;

      @*/
    public void setMarca(String marca) {
        if (marca == null) {
            throw new IllegalArgumentException("La marca non può essere null o vuota");
        }
        boolean isAllWhitespace = true;
        /*@ loop_invariant 0 <= i && i <= marca.length(); @*/
        /*@ loop_invariant isAllWhitespace == (\forall int j; 0 <= j < i; marca.charAt(j) <= ' '); @*/
        for (int i = 0; i < marca.length(); i++) {
            if (marca.charAt(i) > ' ') {
                isAllWhitespace = false;
                break;
            }
        }
        if (isAllWhitespace) {
            throw new IllegalArgumentException("La marca non può essere null o vuota");
        }
        this.marca = marca;
    }

    /*@ 
      @ ensures \result == modello; 
      @*/
    public /*@ pure nullable @*/ String getModello() {
        return modello;
    }

    /*@ 
      @ ensures this.modello == modello;

      @*/
    public void setModello(String modello) {
        if (modello == null) {
            throw new IllegalArgumentException("Il modello non può essere null o vuoto");
        }
        boolean isAllWhitespace = true;
        /*@ loop_invariant 0 <= i && i <= modello.length(); @*/
        /*@ loop_invariant isAllWhitespace == (\forall int j; 0 <= j < i; modello.charAt(j) <= ' '); @*/
        for (int i = 0; i < modello.length(); i++) {
            if (modello.charAt(i) > ' ') {
                isAllWhitespace = false;
                break;
            }
        }
        if (isAllWhitespace) {
            throw new IllegalArgumentException("Il modello non può essere null o vuoto");
        }
        this.modello = modello;
    }

    /*@ 
      @ ensures \result == immagine; 
      @*/
    public /*@ pure nullable @*/ String getImmagine() {
        return immagine;
    }

    /*@ 
      @ ensures this.immagine == immagine; 
      @*/
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    /*@ 
      @ ensures \result == descrizione; 
      @*/
    public /*@ pure nullable @*/ String getDescrizione() {
        return descrizione;
    }

    /*@ 
      @ ensures this.descrizione == descrizione;

      @*/
    public void setDescrizione(String descrizione) {
        if (descrizione == null) {
            throw new IllegalArgumentException("La descrizione non può essere null o vuota");
        }
        boolean isAllWhitespace = true;
        /*@ loop_invariant 0 <= i && i <= descrizione.length(); @*/
        /*@ loop_invariant isAllWhitespace == (\forall int j; 0 <= j < i; descrizione.charAt(j) <= ' '); @*/
        for (int i = 0; i < descrizione.length(); i++) {
            if (descrizione.charAt(i) > ' ') {
                isAllWhitespace = false;
                break;
            }
        }
        if (isAllWhitespace) {
            throw new IllegalArgumentException("La descrizione non può essere null o vuota");
        }
        this.descrizione = descrizione;
    }

    /*@ 
      @ ensures \result == categoria; 
      @*/
    public /*@ pure nullable @*/ Categoria getCategoria() {
        return categoria;
    }

    /*@ 
      @ ensures this.categoria == categoria;

      @*/
    public void setCategoria(Categoria categoria) {
        if (categoria == null) {
            throw new IllegalArgumentException("La categoria non può essere null");
        }
        this.categoria = categoria;
    }
}
