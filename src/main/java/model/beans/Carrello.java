package model.beans;

import java.util.ArrayList;

public class Carrello {
    /*@ spec_public @*/
    private ArrayList<ProdottoCarrello> prodotti;

    /*@ public invariant prodotti != null; @*/
    /*@ public invariant (\forall int i; 0 <= i && i < prodotti.size(); prodotti.get(i) != null); @*/

    /*@
      @ assignable prodotti;
      @ ensures prodotti != null && prodotti.isEmpty();
      @*/
    public Carrello() {
        prodotti = new ArrayList<>();
    }

    /*@
      @ ensures \result >= 0.0;
      @ pure
      @*/
    public double getTotaleCarrello() {
        double totale = 0.0;
        for (ProdottoCarrello e : prodotti) {
            totale += e.getPrezzoTotale();
        }
        return totale;
    }

    /*@
      @ ensures \result == prodotti;
      @ pure
      @*/
    public ArrayList<ProdottoCarrello> getProdotti() {
        return prodotti;
    }

    /*@
      @ public normal_behavior
      @   requires p != null;
      @   assignable prodotti;
      @   ensures prodotti.contains(p);
      @   ensures prodotti.size() == \old(prodotti.size()) + 1;
      @   ensures \result == true;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires p == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public boolean aggiungiProdotto(ProdottoCarrello p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da aggiungere non può essere null");
        }
        return prodotti.add(p);
    }

    /*@
      @ public normal_behavior
      @   requires p != null;
      @   assignable prodotti;
      @   ensures (\forall ProdottoCarrello pc; prodotti.contains(pc); pc.getProdotto().getId() != p.getId());
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires p == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void eliminaProdotto(Prodotto p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da eliminare non può essere null");
        }
        prodotti.removeIf(e -> e.getProdotto().getId() == p.getId());
    }

    /*@
      @ public normal_behavior
      @   requires p != null && qnt > 0;
      @   requires (\exists ProdottoCarrello pc; prodotti.contains(pc); pc.getProdotto().getId() == p.getId());
      @   assignable prodotti.get(*).quantita; 
      @   ensures (\exists ProdottoCarrello pc; prodotti.contains(pc); pc.getProdotto().getId() == p.getId() && pc.getQuantita() == qnt);
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires p == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires qnt <= 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires p != null && qnt > 0 && !(\exists ProdottoCarrello pc; prodotti.contains(pc); pc.getProdotto().getId() == p.getId());
      @   assignable \nothing;
      @   signals (IllegalStateException e) true;
      @*/
    public void cambiaQuantita(Prodotto p, int qnt) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        if (qnt <= 0) {
            throw new IllegalArgumentException("La quantità deve essere maggiore di zero");
        }
        for (ProdottoCarrello pc : prodotti) {
            if (pc.getProdotto().getId() == p.getId()) {
                pc.setQuantita(qnt);
                return;
            }
        }
        // Product not found
        throw new IllegalStateException("Il prodotto con id " + p.getId() + " non è presente nel carrello");
    }
}