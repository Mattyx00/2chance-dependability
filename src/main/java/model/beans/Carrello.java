package model.beans;

import java.util.ArrayList;

public class Carrello {
    /* @ spec_public @ */
    private ArrayList<ProdottoCarrello> prodotti;

    /* @ public invariant prodotti != null; @ */

    /*
     * @
     * 
     * @ ensures prodotti != null && prodotti.isEmpty();
     * 
     * @
     */
    public Carrello() {
        prodotti = new ArrayList<>();
    }

    /*
     * @
     * 
     * @ ensures \result >= 0.0;
     * 
     * @
     */
    public double getTotaleCarrello() {
        double totale = 0.0;
        for (ProdottoCarrello e : prodotti) {
            totale += e.getPrezzoTotale();
        }
        return totale;
    }

    /*
     * @
     * 
     * @ ensures \result == prodotti;
     * 
     * @
     */
    public ArrayList<ProdottoCarrello> getProdotti() {
        return prodotti;
    }

    /*
     * @
     * 
     * @ requires p != null;
     * 
     * @ ensures prodotti.contains(p);
     * 
     * @
     */
    public boolean aggiungiProdotto(ProdottoCarrello p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da aggiungere non può essere null");
        }
        return prodotti.add(p);
    }

    /*
     * @
     * 
     * @ requires p != null;
     * 
     * @
     */
    public void eliminaProdotto(Prodotto p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da eliminare non può essere null");
        }
        prodotti.removeIf(e -> e.getProdotto().getId() == p.getId());
    }

    /*
     * @
     * 
     * @ requires p != null;
     * 
     * @ requires qnt > 0;
     * 
     * @
     */
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
        // Product not found - throw exception for consistency
        throw new IllegalStateException("Il prodotto con id " + p.getId() + " non è presente nel carrello");
    }
}
