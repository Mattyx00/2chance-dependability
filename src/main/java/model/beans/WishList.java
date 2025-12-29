package model.beans;

import java.util.ArrayList;

public class WishList {
    /*@ spec_public nullable @*/
    private Utente utente;
    /*@ spec_public @*/
    private ArrayList<Prodotto> prodotti;

    /*@ public invariant prodotti != null; @*/

    /*@
      @ public normal_behavior
      @   requires true;
      @   assignable prodotti;
      @   ensures prodotti != null;
      @   ensures utente == null;
      @*/
    public WishList() {
        prodotti = new ArrayList<>();
    }

    /*@
      @ public normal_behavior
      @   requires utente != null;
      @   assignable this.utente, this.prodotti;
      @   ensures this.utente == utente;
      @   ensures this.prodotti != null && this.prodotti.isEmpty();
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires utente == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
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
      @ pure
      @*/
    public Utente getUtente() {
        return utente;
    }

    /*@
      @ public normal_behavior
      @   requires utente != null;
      @   assignable this.utente;
      @   ensures this.utente == utente;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires utente == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
    }

    /*@ 
      @ ensures \result == prodotti;
      @ pure
      @*/
    public ArrayList<Prodotto> getProdotti() {
        return prodotti;
    }

    /*@
      @ public normal_behavior
      @   requires prodotti != null;
      @   assignable this.prodotti;
      @   ensures this.prodotti == prodotti;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires prodotti == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setProdotti(ArrayList<Prodotto> prodotti) {
        if (prodotti == null) {
            throw new IllegalArgumentException("La lista dei prodotti non può essere null");
        }
        this.prodotti = prodotti;
    }
}
