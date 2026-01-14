package model.beans;

import java.util.ArrayList;

public class WishList {

    /*@ spec_public @*/
    private Utente utente;
    /*@ spec_public @*/
    private ArrayList<Prodotto> prodotti;

    /*@
      @ public invariant utente != null;
      @ public invariant prodotti != null;
      @*/

    /*@
      @ ensures utente != null;
      @ ensures prodotti != null;
      @*/
    public WishList() {
        this.utente = new Utente();
        prodotti = new ArrayList<>();
    }

    /*@
      @ requires utente != null;
      @ ensures this.utente == utente;
      @ ensures prodotti != null;
      @*/
    public WishList(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
        this.prodotti = new ArrayList<>();
    }

    /*@
      @ ensures \result == utente;
      @ ensures \result != null;
      @*/
    public Utente getUtente() {
        return utente;
    }

    /*@
      @ requires utente != null;
      @ ensures this.utente == utente;
      @*/
    public void setUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
    }

    /*@
      @ ensures \result == prodotti;
      @ ensures \result != null;
      @*/
    public ArrayList<Prodotto> getProdotti() {
        return prodotti;
    }

    /*@
      @ requires prodotti != null;
      @ ensures this.prodotti == prodotti;
      @*/
    public void setProdotti(ArrayList<Prodotto> prodotti) {
        if (prodotti == null) {
            throw new IllegalArgumentException("La lista dei prodotti non può essere null");
        }
        this.prodotti = prodotti;
    }
}
