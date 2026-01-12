package model.beans;

import java.util.ArrayList;

public class Carrello {
    private ArrayList<ProdottoCarrello> prodotti;

    public Carrello() {
        prodotti = new ArrayList<>();
    }

    public double getTotaleCarrello() {
        double totale = 0.0;
        for (ProdottoCarrello e : prodotti) {
            totale += e.getPrezzoTotale();
        }
        return totale;
    }

    public ArrayList<ProdottoCarrello> getProdotti() {
        return prodotti;
    }

    public boolean aggiungiProdotto(ProdottoCarrello p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da aggiungere non può essere null");
        }
        return prodotti.add(p);
    }

    public void eliminaProdotto(Prodotto p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto da eliminare non può essere null");
        }
        prodotti.removeIf(e -> e.getProdotto().getId() == p.getId());
    }

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