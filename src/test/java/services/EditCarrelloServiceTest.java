// java
        package services;

import model.beans.Carrello;
import model.beans.Prodotto;
import model.beans.ProdottoCarrello;
import model.dao.ProdottoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.MockedConstruction;
import org.mockito.Mockito;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class EditCarrelloServiceTest {

    private EditCarrelloService service;

    @BeforeEach
    void setUp() {
        service = new EditCarrelloService();
    }

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

        try (MockedConstruction<ProdottoDAO> mocked = Mockito.mockConstruction(ProdottoDAO.class, (mock, context) -> {
            when(mock.getProdottoById(5)).thenReturn(p);
        })) {
            // Act
            Carrello result = service.eliminaProdotto(carrello, 5);

            // Assert
            assertNotNull(result);
            assertTrue(result.getProdotti().isEmpty(), "Il carrello deve essere vuoto dopo l'eliminazione");
        }
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

        try (MockedConstruction<ProdottoDAO> mocked = Mockito.mockConstruction(ProdottoDAO.class, (mock, context) -> {
            when(mock.getProdottoById(7)).thenReturn(p);
        })) {
            // Act
            Carrello result = service.modificaQuantitaProdotto(carrello, 7, 3);

            // Assert
            assertNotNull(result);
            assertEquals(1, result.getProdotti().size());
            assertEquals(3, result.getProdotti().get(0).getQuantita());
        }
    }
}
