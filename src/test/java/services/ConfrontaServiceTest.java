package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ConfrontaServiceTest {

    @Mock
    private ProdottoDAO prodottoDAO;

    @InjectMocks
    private ConfrontaService service;

    @Test
    void testConfrontaProdotti_RestituisceDueProdotti() throws SQLException {
        // Arrange
        Prodotto p1 = new Prodotto();
        p1.setId(1);
        p1.setMarca("MarcaA");
        p1.setModello("ModelloA");
        p1.setPrezzo(10.0);

        Prodotto p2 = new Prodotto();
        p2.setId(2);
        p2.setMarca("MarcaB");
        p2.setModello("ModelloB");
        p2.setPrezzo(20.0);

        when(prodottoDAO.getProdottoById(1)).thenReturn(p1);
        when(prodottoDAO.getProdottoById(2)).thenReturn(p2);

        // Act
        Prodotto[] result = service.confrontaProdotti(1, 2);

        // Assert
        assertNotNull(result);
        assertEquals(2, result.length);

        Prodotto r1 = result[0];
        Prodotto r2 = result[1];

        assertNotNull(r1);
        assertNotNull(r2);

        assertEquals(1, r1.getId());
        assertEquals("MarcaA", r1.getMarca());
        assertEquals("ModelloA", r1.getModello());
        assertEquals(10.0, r1.getPrezzo());

        assertEquals(2, r2.getId());
        assertEquals("MarcaB", r2.getMarca());
        assertEquals("ModelloB", r2.getModello());
        assertEquals(20.0, r2.getPrezzo());
    }
}
