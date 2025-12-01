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
class AggiungiCarrelloServiceTest {

    private AggiungiCarrelloService service;

    @BeforeEach
    void setUp() {
        service = new AggiungiCarrelloService();
    }

    @Test
    void testAggiungiAlCarrello_CarrelloNull() throws SQLException {
        // Arrange
        Prodotto p1 = new Prodotto();
        p1.setId(1);
        p1.setMarca("Marca1");
        p1.setModello("Modello1");
        p1.setPrezzo(50.0);

        try (MockedConstruction<ProdottoDAO> mocked = Mockito.mockConstruction(ProdottoDAO.class, (mock, context) -> {
            when(mock.getProdottoById(1)).thenReturn(p1);
        })) {
            // Act
            Carrello result = service.aggiungiAlCarrello(null, 1, 2);

            // Assert
            assertNotNull(result);
            assertEquals(1, result.getProdotti().size());
            ProdottoCarrello pc = result.getProdotti().get(0);
            assertEquals(1, pc.getProdotto().getId());
            assertEquals(2, pc.getQuantita());
        }
    }

    @Test
    void testAggiungiAlCarrello_ProdottoEsistenteIncrementaQuantita() throws SQLException {
        // Arrange
        Prodotto p1 = new Prodotto();
        p1.setId(1);
        p1.setMarca("Marca1");

        Carrello carrello = new Carrello();
        ProdottoCarrello existing = new ProdottoCarrello();
        existing.setProdotto(p1);
        existing.setQuantita(1);
        carrello.aggiungiProdotto(existing);

        try (MockedConstruction<ProdottoDAO> mocked = Mockito.mockConstruction(ProdottoDAO.class, (mock, context) -> {
            when(mock.getProdottoById(1)).thenReturn(p1);
        })) {
            // Act
            Carrello result = service.aggiungiAlCarrello(carrello, 1, 2);

            // Assert
            assertNotNull(result);
            assertEquals(1, result.getProdotti().size());
            assertEquals(3, result.getProdotti().get(0).getQuantita());
        }
    }
}
