package services;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.dao.CategoriaDAO;
import model.dao.OrdineDAO;
import model.dao.ProdottoDAO;
import model.dao.UtenteDAO;
import org.json.JSONObject;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class AdminServiceTest {

    @Mock
    private ProdottoDAO prodottoDAO;
    @Mock
    private CategoriaDAO categoriaDAO;
    @Mock
    private UtenteDAO utenteDAO;
    @Mock
    private OrdineDAO ordineDAO;

    private AdminService adminService;

    @BeforeEach
    void setUp() {
        adminService = new AdminService(prodottoDAO, categoriaDAO, utenteDAO, ordineDAO);
    }

    @Test
    void testMostraProdotti() throws IOException, SQLException {
        // Arrange
        ArrayList<Prodotto> prodotti = new ArrayList<>();
        Prodotto p1 = new Prodotto();
        p1.setId(1);
        p1.setMarca("Marca1");
        p1.setModello("Modello1");
        p1.setPrezzo(100.0);
        Categoria c1 = new Categoria();
        c1.setNomeCategoria("Elettronica");
        p1.setCategoria(c1);
        prodotti.add(p1);

        when(prodottoDAO.getProdotti()).thenReturn(prodotti);

        // Act
        String result = adminService.mostraProdotti();

        // Assert
        JSONObject jsonResult = new JSONObject(result);
        assertTrue(jsonResult.has("prodotti"));
        assertEquals(1, jsonResult.getJSONArray("prodotti").length());
        
        JSONObject pJson = jsonResult.getJSONArray("prodotti").getJSONObject(0);
        assertEquals(1, pJson.getInt("id"));
        assertEquals("Marca1", pJson.getString("marca"));
        assertEquals("Modello1", pJson.getString("modello"));
        assertEquals("Elettronica", pJson.getString("categoria"));
        assertEquals(100.0, pJson.getDouble("prezzo"));
    }
}
