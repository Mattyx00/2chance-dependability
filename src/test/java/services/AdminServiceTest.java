package services;

import model.beans.Categoria;
import model.beans.Ordine;
import model.beans.Prodotto;
import model.beans.Utente;
import model.dao.CategoriaDAO;
import model.dao.OrdineDAO;
import model.dao.ProdottoDAO;
import model.dao.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import javax.servlet.http.Part;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.doNothing;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.junit.jupiter.MockitoExtension;

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
    @Mock
    private Part part;

    @InjectMocks
    private AdminService adminService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should instantiate service when all DAOs are non-null")
    void shouldInstantiateServiceWhenAllDAOsAreNonNull() {
        // Assert
        assertNotNull(adminService);
    }

    @Test
    @DisplayName("TF2: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenProdottoDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new AdminService(null, categoriaDAO, utenteDAO, ordineDAO));
        assertTrue(exception.getMessage().contains("ProdottoDAO cannot be null"));
    }

    @Test
    @DisplayName("TF3: Should throw exception when CategoriaDAO is null")
    void shouldThrowExceptionWhenCategoriaDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new AdminService(prodottoDAO, null, utenteDAO, ordineDAO));
        assertTrue(exception.getMessage().contains("CategoriaDAO cannot be null"));
    }

    @Test
    @DisplayName("TF4: Should throw exception when UtenteDAO is null")
    void shouldThrowExceptionWhenUtenteDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new AdminService(prodottoDAO, categoriaDAO, null, ordineDAO));
        assertTrue(exception.getMessage().contains("UtenteDAO cannot be null"));
    }

    @Test
    @DisplayName("TF5: Should throw exception when OrdineDAO is null")
    void shouldThrowExceptionWhenOrdineDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new AdminService(prodottoDAO, categoriaDAO, utenteDAO, null));
        assertTrue(exception.getMessage().contains("OrdineDAO cannot be null"));
    }

    // =================================================================================================
    // aggiungiProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("TF6: Should add product when inputs are valid")
    void shouldAddProdottoWhenInputsAreValid() throws Exception {
        // Arrange
        Prodotto product = new Prodotto();
        Categoria category = new Categoria();
        String jsonSpecifications = "{\"specifiche\":[{\"nome\":\"Colore\",\"valore\":\"Rosso\"}]}";

        String fakeImageName = "image.jpg";
        byte[] fakeImageRawStream = "test data".getBytes();
        ByteArrayInputStream fakeImageStream = new ByteArrayInputStream(fakeImageRawStream);

        when(part.getSubmittedFileName()).thenReturn(fakeImageName);
        when(part.getInputStream()).thenReturn(fakeImageStream);
        when(prodottoDAO.getLastProduct()).thenReturn(1);
        when(prodottoDAO.addProdotto(product)).thenReturn(1);
        doNothing().when(prodottoDAO).aggiungiSpecifiche(any(), anyInt());

        // Act
        adminService.aggiungiProdotto(product, category, part, jsonSpecifications);

        // Assert
        assertAll("Verify interactions",
                () -> verify(prodottoDAO).addProdotto(product),
                () -> verify(prodottoDAO).aggiungiSpecifiche(any(), eq(1)),
                () -> assertEquals("image.jpg", product.getImmagine()));
    }

    @Test
    @DisplayName("TF7: Should throw exception when Prodotto is null")
    void shouldThrowExceptionWhenProdottoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(null, new Categoria(), part, "{}"));
        assertTrue(exception.getMessage().contains("Prodotto cannot be null"));
    }

    @Test
    @DisplayName("TF8: Should throw exception when Categoria is null")
    void shouldThrowExceptionWhenCategoriaIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(new Prodotto(), null, part, "{}"));
        assertTrue(exception.getMessage().contains("Categoria cannot be null"));
    }

    @Test
    @DisplayName("TF9: Should throw exception when Immagine is null")
    void shouldThrowExceptionWhenImmagineIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(new Prodotto(), new Categoria(), null, "{}"));
        assertTrue(exception.getMessage().contains("Immagine Part cannot be null"));
    }

    @ParameterizedTest
    @DisplayName("TF10, TF11: Should throw exception when Specifiche is null or empty")
    @CsvSource({ ",", "''", "'   '" })
    void shouldThrowExceptionWhenSpecificheIsInvalid(String specifiche) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(new Prodotto(), new Categoria(), part, specifiche));
        assertTrue(exception.getMessage().contains("Specifiche string cannot be null or empty"));
    }

    @Test
    @DisplayName("TF12: Should throw exception when Image file name is null")
    void shouldThrowExceptionWhenImageFileNameIsNull() {
        // Act & Assert
        when(part.getSubmittedFileName()).thenReturn(null);
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(new Prodotto(), new Categoria(), part, "{}"));
        assertTrue(exception.getMessage().contains("Image file name cannot be null"));
    }

    @Test
    @DisplayName("TF13: Should throw exception when Specifiche is invalid JSON")
    void shouldThrowExceptionWhenSpecificheIsInvalidJson() {
        // Act & Assert
        when(part.getSubmittedFileName()).thenReturn("img.jpg");
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(new Prodotto(), new Categoria(), part, "{invalid_json}"));
        assertTrue(exception.getMessage().contains("Invalid JSON format for specifiche"));
    }

    @Test
    @DisplayName("TF14: Should throw exception when getLastProduct returns invalid ID")
    void shouldThrowExceptionWhenLastProductIdIsInvalid() throws Exception {
        // Act & Assert
        Prodotto product = new Prodotto();
        Categoria category = new Categoria();
        String jsonSpecifiche = "{\"specifiche\":[]}";

        when(part.getSubmittedFileName()).thenReturn("image.jpg");
        when(part.getInputStream()).thenReturn(new ByteArrayInputStream("test".getBytes()));
        when(prodottoDAO.getLastProduct()).thenReturn(0);

        assertThrows(IllegalStateException.class,
                () -> adminService.aggiungiProdotto(product, category, part, jsonSpecifiche),
                "Failed to retrieve the last added product ID.");
    }

    // =================================================================================================
    // mostraProdotti Tests
    // =================================================================================================

    @Test
    @DisplayName("TF15: Should return JSON when products exist")
    void shouldReturnJsonWhenProductsExist() throws Exception {
        ArrayList<Prodotto> list = new ArrayList<>();
        Prodotto product = new Prodotto();
        product.setId(1);
        product.setMarca("Marca");
        product.setModello("Modello");
        product.setPrezzo(10.0f);
        Categoria category = new Categoria();
        category.setNomeCategoria("Cat");
        product.setCategoria(category);
        list.add(product);

        when(prodottoDAO.getProdotti()).thenReturn(list);

        String json = adminService.mostraProdotti();
        assertTrue(json.contains("\"prodotti\":"));
        assertTrue(json.contains("\"marca\":\"Marca\""));
    }

    @Test
    @DisplayName("TF16: Should throw exception when DAO returns null")
    void shouldThrowExceptionWhenDaoReturnsNullForProdotti() throws Exception {
        when(prodottoDAO.getProdotti()).thenReturn(null);
        assertThrows(IllegalStateException.class, () -> adminService.mostraProdotti());
    }

    @Test
    @DisplayName("TF17: Should handle null elements in product list")
    void shouldHandleNullElementsInProductList() throws Exception {
        ArrayList<Prodotto> list = new ArrayList<>();
        list.add(null);
        Prodotto product = new Prodotto();
        product.setId(1);
        // Minimal setup
        list.add(product);

        when(prodottoDAO.getProdotti()).thenReturn(list);
        String json = adminService.mostraProdotti();
        assertTrue(json.contains("\"prodotti\":"));
        // Expect only 1 product in the array (the non-null one)
    }

    // =================================================================================================
    // eliminaProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("TF18: Should delete product when ID is positive")
    void shouldEliminaProdottoWhenIdIsPositive() throws Exception {
        adminService.eliminaProdotto(10);
        verify(prodottoDAO).eliminaProdotto(10);
    }

    @ParameterizedTest
    @DisplayName("TF19, TF20: Should throw exception when ID is invalid")
    @ValueSource(ints = { 0, -1 })
    void shouldThrowExceptionWhenEliminaProdottoIdIsInvalid(int id) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.eliminaProdotto(id));
        assertTrue(exception.getMessage().contains("Invalid product ID"));
    }

    // =================================================================================================
    // mostraCategorie Tests
    // =================================================================================================

    @Test
    @DisplayName("TF21: Should return JSON when categories exist")
    void shouldReturnJsonWhenCategoriesExist() throws Exception {
        ArrayList<Categoria> list = new ArrayList<>();
        Categoria category = new Categoria();
        category.setNomeCategoria("TestCat");
        list.add(category);

        when(categoriaDAO.getCategorie()).thenReturn(list);

        String json = adminService.mostraCategorie();
        assertTrue(json.contains("TestCat"));
    }

    @Test
    @DisplayName("TF22: Should throw exception when DAO returns null for categories")
    void shouldThrowExceptionWhenCategoriaDaoReturnsNull() throws Exception {
        when(categoriaDAO.getCategorie()).thenReturn(null);
        assertThrows(IllegalStateException.class, () -> adminService.mostraCategorie());
    }

    // =================================================================================================
    // aggiungiCategoria Tests
    // =================================================================================================

    @Test
    @DisplayName("TF23: Should add category when name is valid")
    void shouldAddCategoriaWhenNameIsValid() throws Exception {
        adminService.aggiungiCategoria("NewCat");
        verify(categoriaDAO).addCategoria(any(Categoria.class));
    }

    @ParameterizedTest
    @DisplayName("TF24, TF25: Should throw exception when category name is invalid")
    @CsvSource({ ",", "''", "'   '" })
    void shouldThrowExceptionWhenCategoriaNameIsInvalid(String nome) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiCategoria(nome));
        assertTrue(exception.getMessage().contains("Invalid category name"));
    }

    // =================================================================================================
    // eliminaCategoria Tests
    // =================================================================================================

    @Test
    @DisplayName("TF26: Should delete category when name is valid")
    void shouldEliminaCategoriaWhenNameIsValid() throws Exception {
        adminService.eliminaCategoria("OldCat");
        verify(categoriaDAO).eliminaCategoria("OldCat");
    }

    @ParameterizedTest
    @DisplayName("TF27, TF28: Should throw exception when category name is invalid for deletion")
    @CsvSource({ ",", "''", "'   '" })
    void shouldThrowExceptionWhenEliminaCategoriaNameIsInvalid(String nome) {
        assertThrows(IllegalArgumentException.class, () -> adminService.eliminaCategoria(nome));
    }

    // =================================================================================================
    // mostraUtenti Tests
    // =================================================================================================

    @Test
    @DisplayName("TF29: Should return JSON when users exist")
    void shouldReturnJsonWhenUtentiExist() throws Exception {
        ArrayList<Utente> list = new ArrayList<>();
        Utente user = new Utente();
        user.setNome("Mario");
        user.setCognome("Rossi");
        list.add(user);

        when(utenteDAO.getUtenti()).thenReturn(list);

        String json = adminService.mostraUtenti();
        assertTrue(json.contains("Mario"));
        assertTrue(json.contains("Rossi"));
    }

    @Test
    @DisplayName("TF30: Should throw exception when DAO returns null for users")
    void shouldThrowExceptionWhenUtenteDaoReturnsNull() throws Exception {
        when(utenteDAO.getUtenti()).thenReturn(null);
        assertThrows(IllegalStateException.class, () -> adminService.mostraUtenti());
    }

    // =================================================================================================
    // mostraOrdini Tests
    // =================================================================================================

    @Test
    @DisplayName("TF31: Should return JSON when orders exist")
    void shouldReturnJsonWhenOrdiniExist() throws Exception {
        ArrayList<Ordine> list = new ArrayList<>();
        Ordine order = new Ordine();
        order.setId(1);
        list.add(order);

        when(ordineDAO.getOrdini()).thenReturn(list);

        String json = adminService.mostraOrdini();
        assertTrue(json.contains("\"ordini\":"));
    }

    @Test
    @DisplayName("TF32: Should throw exception when DAO returns null for orders")
    void shouldThrowExceptionWhenOrdineDaoReturnsNull() throws Exception {
        when(ordineDAO.getOrdini()).thenReturn(null);
        assertThrows(IllegalStateException.class, () -> adminService.mostraOrdini());
    }

    // =================================================================================================
    // infoOrdine Tests
    // =================================================================================================

    @Test
    @DisplayName("TF33: Should return detailed JSON when order and cart exist")
    void shouldReturnInfoOrdineWhenOrderExists() throws Exception {
        Ordine order = new Ordine();
        order.setId(1);

        model.beans.Carrello carrello = mock(model.beans.Carrello.class);
        ArrayList<model.beans.ProdottoCarrello> prodotti = new ArrayList<>();
        model.beans.ProdottoCarrello pc = new model.beans.ProdottoCarrello();
        Prodotto p = new Prodotto();
        p.setId(10);
        p.setPrezzo(100f);
        pc.setProdotto(p);
        pc.setQuantita(2);
        prodotti.add(pc);

        when(carrello.getProdotti()).thenReturn(prodotti);
        when(carrello.getTotaleCarrello()).thenReturn(200.0);

        when(ordineDAO.getOrdineById(1)).thenReturn(order);
        when(ordineDAO.getProdottoOrdine(order)).thenReturn(carrello);

        String json = adminService.infoOrdine(1);
        assertTrue(json.contains("\"prodotti\":"));
        assertTrue(json.contains("100"));
    }

    @ParameterizedTest
    @DisplayName("TF34, TF35: Should throw exception when order ID is invalid")
    @ValueSource(ints = { 0, -1 })
    void shouldThrowExceptionWhenInfoOrdineIdIsInvalid(int id) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.infoOrdine(id));
        assertTrue(exception.getMessage().contains("Invalid order ID"));
    }

    @Test
    @DisplayName("TF34 (Null): Should throw exception when order ID is null")
    void shouldThrowExceptionWhenInfoOrdineIdIsNull() {
        assertThrows(IllegalArgumentException.class, () -> adminService.infoOrdine(null));
    }

    @Test
    @DisplayName("TF36: Should throw exception when order not found")
    void shouldThrowExceptionWhenOrderNotFound() throws Exception {
        when(ordineDAO.getOrdineById(999)).thenReturn(null);
        assertThrows(IllegalArgumentException.class, () -> adminService.infoOrdine(999));
    }

    @Test
    @DisplayName("TF37: Should throw exception when cart is null")
    void shouldThrowExceptionWhenCartIsNull() throws Exception {
        Ordine o = new Ordine();
        when(ordineDAO.getOrdineById(1)).thenReturn(o);
        when(ordineDAO.getProdottoOrdine(o)).thenReturn(null);

        assertThrows(IllegalStateException.class, () -> adminService.infoOrdine(1));
    }

    // =================================================================================================
    // getProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("TF38: Should return JSON when product exists")
    void shouldReturnJsonWhenProductExists() throws Exception {
        Prodotto p = new Prodotto();
        p.setId(5);
        p.setMarca("Sony");
        p.setModello("PS5");

        when(prodottoDAO.getProdottoById(5)).thenReturn(p);

        String json = adminService.getProdotto(5);
        assertTrue(json.contains("Sony"));
        assertTrue(json.contains("PS5"));
    }

    @ParameterizedTest
    @DisplayName("TF39, TF40: Should throw exception when product ID is invalid")
    @ValueSource(ints = { 0, -1 })
    void shouldThrowExceptionWhenGetProdottoIdIsInvalid(int id) {
        assertThrows(IllegalArgumentException.class, () -> adminService.getProdotto(id));
    }

    @Test
    @DisplayName("TF39 (Null): Should throw exception when product ID is null")
    void shouldThrowExceptionWhenGetProdottoIdIsNull() {
        assertThrows(IllegalArgumentException.class, () -> adminService.getProdotto(null));
    }

    @Test
    @DisplayName("TF41: Should throw exception when product not found")
    void shouldThrowExceptionWhenProductNotFound() throws Exception {
        when(prodottoDAO.getProdottoById(999)).thenReturn(null);
        assertThrows(IllegalArgumentException.class, () -> adminService.getProdotto(999));
    }

    // =================================================================================================
    // modificaProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("TF42: Should modify product when inputs are valid and image provided")
    void shouldModificaProdottoWhenInputsAreValid() throws Exception {
        Prodotto p = new Prodotto();
        p.setId(1);
        Categoria c = new Categoria();
        String jsonSpec = "{\"specifiche\":[{\"nome\":\"A\",\"valore\":\"B\"}]}";

        when(part.getSize()).thenReturn(100L);
        when(part.getSubmittedFileName()).thenReturn("new.jpg");
        // Mock file stream to avoid IO errors, though actual file write is hard to
        // avoid without Powermock or abstraction.
        // We rely on simple byte stream mocking.
        when(part.getInputStream()).thenReturn(new ByteArrayInputStream("data".getBytes()));

        doNothing().when(prodottoDAO).modificaProdotto(p);
        doNothing().when(prodottoDAO).eliminaSpecificheProdotto(1);
        doNothing().when(prodottoDAO).aggiungiSpecifiche(any(), eq(1));

        adminService.modificaProdotto(p, c, part, jsonSpec);

        verify(prodottoDAO).modificaProdotto(p);
        verify(prodottoDAO).eliminaSpecificheProdotto(1);
        verify(prodottoDAO).aggiungiSpecifiche(any(), eq(1));
    }

    @Test
    @DisplayName("TF43: Should modify product when image is null (no image update)")
    void shouldModificaProdottoWhenImageIsNull() throws Exception {
        Prodotto p = new Prodotto();
        p.setId(1);
        Categoria c = new Categoria();
        String jsonSpec = "{\"specifiche\":[]}";

        adminService.modificaProdotto(p, c, null, jsonSpec);

        verify(prodottoDAO).modificaProdotto(p);
        // p.setImmagine(null) should be called or implied
    }

    @Test
    @DisplayName("TF44: Should throw exception when Prodotto is null (modifica)")
    void shouldThrowExceptionWhenModificaProdottoIsNull() {
        assertThrows(IllegalArgumentException.class,
                () -> adminService.modificaProdotto(null, new Categoria(), part, "{}"));
    }

    @Test
    @DisplayName("TF45: Should throw exception when Categoria is null (modifica)")
    void shouldThrowExceptionWhenModificaCategoriaIsNull() {
        assertThrows(IllegalArgumentException.class,
                () -> adminService.modificaProdotto(new Prodotto(), null, part, "{}"));
    }

    @Test
    @DisplayName("TF46: Should throw exception when Specifiche is null (modifica)")
    void shouldThrowExceptionWhenModificaSpecificheIsNull() {
        assertThrows(IllegalArgumentException.class,
                () -> adminService.modificaProdotto(new Prodotto(), new Categoria(), part, null));
    }

    @Test
    @DisplayName("TF47: Should throw exception when Specifiche is invalid JSON (modifica)")
    void shouldThrowExceptionWhenModificaSpecificheIsInvalidJson() {
        assertThrows(IllegalArgumentException.class,
                () -> adminService.modificaProdotto(new Prodotto(), new Categoria(), part, "{invalid"));
    }
}
