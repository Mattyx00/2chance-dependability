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
        for (ProdottoCarrello e : prodotti) {
            if (e.getProdotto().getId() == p.getId()) {
                prodotti.remove(e);
            }
        }
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
        for (int i = 0; i < prodotti.size(); i++) {
            if (prodotti.get(i).getProdotto().getId() == p.getId()) {
                prodotti.get(i).setQuantita(qnt);
            }
        }
    }
}
