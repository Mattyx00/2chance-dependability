package model.beans;

import java.util.ArrayList;

public class Carrello {

    /*@ public invariant prodotti != null; @*/
    /*@ spec_public @*/
    private ArrayList<ProdottoCarrello> prodotti;

    /*@
      @ ensures prodotti != null && prodotti.isEmpty();
      @*/
    public Carrello() {
        prodotti = new ArrayList<>();
    }

    /*@
      @ ensures \result >= 0.0;
      @*/
    public double getTotaleCarrello() {
        double totale = 0.0;
        /*@
          @ loop_invariant i >= 0 && i <= prodotti.size();
          @ loop_invariant totale >= 0.0;
          @*/
        for (int i = 0; i < prodotti.size(); i++) {
            ProdottoCarrello e = prodotti.get(i);
            totale += e.getPrezzoTotale();
        }
        return totale;
    }

    /*@
      @ ensures \result != null;
      @ ensures \result == prodotti;
      @*/
    public ArrayList<ProdottoCarrello> getProdotti() {
        return prodotti;
    }

    /*@
      @ requires p != null;
      @ ensures \result == true;
      @ ensures prodotti.contains(p);

      @*/
    public boolean aggiungiProdotto(ProdottoCarrello p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da aggiungere non può essere null");
        }
        return prodotti.add(p);
    }

    /*@
      @ requires p != null;

      @*/
    public void eliminaProdotto(Prodotto p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da eliminare non può essere null");
        }
        /*@
          @ loop_invariant i >= 0 && i <= prodotti.size();
          @*/
        for (int i = 0; i < prodotti.size(); i++) {
            ProdottoCarrello e = prodotti.get(i);
            if (e.getProdotto().getId() == p.getId()) {
                prodotti.remove(i);
                i--;
            }
        }
    }

    /*@
      @ requires p != null;
      @ requires qnt > 0;


      @*/
    public void cambiaQuantita(Prodotto p, int qnt) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        if (qnt <= 0) {
            throw new IllegalArgumentException("La quantità deve essere maggiore di zero");
        }
        /*@
          @ loop_invariant i >= 0 && i <= prodotti.size();
          @*/
        for (int i = 0; i < prodotti.size(); i++) {
            ProdottoCarrello pc = prodotti.get(i);
            if (pc.getProdotto().getId() == p.getId()) {
                pc.setQuantita(qnt);
                return;
            }
        }
        // Product not found
        throw new IllegalStateException("Il prodotto con id " + p.getId() + " non è presente nel carrello");
    }
}