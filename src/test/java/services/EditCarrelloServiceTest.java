package services;

import model.beans.Carrello;
import model.beans.Prodotto;
import model.beans.ProdottoCarrello;
import model.dao.ProdottoDAO;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class EditCarrelloServiceTest {

    @Mock
    private ProdottoDAO prodottoDAO;

    @InjectMocks
    private EditCarrelloService service;

    @Test
    void testEliminaProdotto_RimuoveProdottoDalCarrello() throws SQLException {
        // Arrange
        Prodotto p = new Prodotto();
        p.setId(5);
        p.setMarca("MarcaX");

        ProdottoCarrello pc = new ProdottoCarrello();
        pc.setProdotto(p);
        pc.setQuantita(1);

        Carrello carrello = new Carrello();
        carrello.aggiungiProdotto(pc);

        when(prodottoDAO.getProdottoById(5)).thenReturn(p);

        // Act
        Carrello result = service.eliminaProdotto(carrello, 5);

        // Assert
        assertNotNull(result);
        assertTrue(result.getProdotti().isEmpty(), "Il carrello deve essere vuoto dopo l'eliminazione");
    }

    @Test
    void testModificaQuantitaProdotto_AggiornaQuantita() throws SQLException {
        // Arrange
        Prodotto p = new Prodotto();
        p.setId(7);
        p.setMarca("MarcaY");

        ProdottoCarrello pc = new ProdottoCarrello();
        pc.setProdotto(p);
        pc.setQuantita(1);

        Carrello carrello = new Carrello();
        carrello.aggiungiProdotto(pc);

        when(prodottoDAO.getProdottoById(7)).thenReturn(p);

        // Act
        Carrello result = service.modificaQuantitaProdotto(carrello, 7, 3);

        // Assert
        assertNotNull(result);
        assertEquals(1, result.getProdotti().size());
        assertEquals(3, result.getProdotti().get(0).getQuantita());
    }
}
