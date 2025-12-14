package services;

import model.beans.Carrello;
import model.beans.Ordine;
import model.beans.Prodotto;
import model.beans.ProdottoCarrello;
import model.beans.Utente;
import model.dao.OrdineDAO;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class CheckOutServiceTest {

    @Mock
    private OrdineDAO ordineDAO;

    @InjectMocks
    private CheckOutService service;

    @Test
    void testEffettuaCheckout_CreaOrdineChiamaDAO() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        utente.setId(1);

        Prodotto prodotto = new Prodotto();
        prodotto.setId(10);
        prodotto.setPrezzo(50.0);

        ProdottoCarrello pc = new ProdottoCarrello();
        pc.setProdotto(prodotto);
        pc.setQuantita(2);

        Carrello carrello = new Carrello();
        carrello.aggiungiProdotto(pc);

        String indirizzo = "Via Test 1";

        // Act
        service.effettuaCheckout(utente, carrello, indirizzo);

        // Assert
        verify(ordineDAO).addOrdine(Mockito.argThat(ordine -> ordine != null
                && ordine.getUtente() != null
                && ordine.getUtente().getId() == 1
                && ordine.getIndirizzo().equals(indirizzo)
                && ordine.getPrezzoTotale() == carrello.getTotaleCarrello()));
    }

    @Test
    void testAggiornaOrdiniUtente_PopolaOrdini() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        utente.setId(2);

        ArrayList<Ordine> ordini = new ArrayList<>();
        Ordine o = new Ordine();
        o.setId(5);
        o.setUtente(utente);
        ordini.add(o);

        when(ordineDAO.getOrdiniByUtente(utente)).thenReturn(ordini);

        // Act
        Utente result = service.aggiornaOrdiniUtente(utente);

        // Assert
        assertNotNull(result);
        assertNotNull(result.getOrdini());
        assertEquals(1, result.getOrdini().size());
        assertEquals(5, result.getOrdini().get(0).getId());
    }
}
