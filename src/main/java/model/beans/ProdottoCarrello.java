package model.beans;

public class ProdottoCarrello {
    /* @ spec_public @ */
    private Prodotto prodotto;
    /* @ spec_public @ */
    private int quantita;

    /* @ public invariant quantita >= 0; @ */

    public ProdottoCarrello() {

    }

    /* @ ensures \result == prodotto; @ */
    public Prodotto getProdotto() {
        return prodotto;
    }

    /* @ ensures \result == quantita; @ */
    public int getQuantita() {
        return quantita;
    }

    /*
     * @
     * 
     * @ requires prodotto != null;
     * 
     * @ ensures \result == prodotto.getPrezzo() * quantita;
     * 
     * @
     */
    public double getPrezzoTotale() {
        return prodotto.getPrezzo() * quantita;
    }

    /* @ ensures this.prodotto == prodotto; @ */
    public void setProdotto(Prodotto prodotto) {
        this.prodotto = prodotto;
    }

    /*
     * @
     * 
     * @ requires quantita >= 0;
     * 
     * @ ensures this.quantita == quantita;
     * 
     * @
     */
    public void setQuantita(int quantita) {
        this.quantita = quantita;
    }
}
