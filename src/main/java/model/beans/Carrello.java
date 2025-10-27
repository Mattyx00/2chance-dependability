package model.beans;

import java.util.ArrayList;

public class Carrello {
    private ArrayList<ProdottoCarrello> prodotti;

    public Carrello(){
        prodotti = new ArrayList<>();
    }

    public double getTotaleCarrello(){
        double totale = 0.0;
        for(ProdottoCarrello e: prodotti){
            totale += e.getPrezzoTotale();
        }
        return totale;
    }

    public ArrayList<ProdottoCarrello> getProdotti() {
        return prodotti;
    }

    public boolean aggiungiProdotto(ProdottoCarrello p){
        return prodotti.add(p);
    }

    public void eliminaProdotto(Prodotto p){
       for(ProdottoCarrello e : prodotti){
           if(e.getProdotto().getId() == p.getId()){
               prodotti.remove(e);
           }
       }
    }

    public void cambiaQuantita(Prodotto p, int qnt){
        for(int i=0; i<prodotti.size(); i++){
            if(prodotti.get(i).getProdotto().getId() == p.getId()){
                prodotti.get(i).setQuantita(qnt);
            }
        }
    }
}
