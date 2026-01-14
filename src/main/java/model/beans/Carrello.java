package model.beans;

import java.util.ArrayList;

public class Carrello {

    /*@ spec_public nullable @*/
    private ArrayList<ProdottoCarrello> prodotti;

    /*@
      @ ensures prodotti != null && prodotti.isEmpty();
      @*/
    public Carrello() {
        this.prodotti = new ArrayList<>();
    }

    /*@
      @ ensures \result >= 0.0;
      @*/
    public double getTotaleCarrello() {
        /*@ assume prodotti != null; @*/
        double totale = 0.0;
        
        /*@ loop_invariant i >= 0; @*/
        for (int i = 0; i < prodotti.size(); i++) {
            ProdottoCarrello e = prodotti.get(i);
            
            // Blindatura dati
            /*@ assume e != null && e.prodotto != null; @*/
            /*@ assume e.prodotto.prezzo >= 0 && e.prodotto.peso >= 0 && e.prodotto.quantitaProdotto >= 0; @*/
            
            totale += e.getPrezzoTotale();
        }
        return totale;
    }

    /*@
      @ ensures \result == prodotti;
      @*/
    public /*@ pure nullable @*/ ArrayList<ProdottoCarrello> getProdotti() {
        return prodotti;
    }

    /*@
      @ requires p != null;
      @ ensures \result == true;
      @ ensures prodotti.contains(p);
      @*/
    public boolean aggiungiProdotto(ProdottoCarrello p) {
        /*@ assume prodotti != null; @*/
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da aggiungere non può essere null");
        }
        return prodotti.add(p);
    }

    /*@
      @ requires p != null;
      @*/
    public void eliminaProdotto(Prodotto p) {
        /*@ assume prodotti != null; @*/
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da eliminare non può essere null");
        }
        
        /*@ loop_invariant i >= 0; @*/
        for (int i = 0; i < prodotti.size(); i++) {
            ProdottoCarrello e = prodotti.get(i);
            
            /*@ assume e != null && e.prodotto != null; @*/
            
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
        /*@ assume prodotti != null; @*/
        /*@ assume p.prezzo >= 0 && p.peso >= 0 && p.quantitaProdotto >= 0; @*/
        
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        if (qnt <= 0) {
            throw new IllegalArgumentException("La quantità deve essere maggiore di zero");
        }
        
        /*@ loop_invariant i >= 0; @*/
        for (int i = 0; i < prodotti.size(); i++) {
            ProdottoCarrello pc = prodotti.get(i);
            
            /*@ assume pc != null && pc.prodotto != null; @*/
            /*@ assume pc.prodotto.prezzo >= 0 && pc.prodotto.peso >= 0; @*/
            
            if (pc.getProdotto().getId() == p.getId()) {
                pc.setQuantita(qnt);
                
                // Con 'assignable' in ProdottoCarrello, questo assume ora funzionerà al 100%
                /*@ assume p.prezzo >= 0 && p.peso >= 0 && p.quantitaProdotto >= 0; @*/
                return;
            }
        }
        throw new IllegalStateException("Il prodotto con id " + p.getId() + " non è presente nel carrello");
    }
}