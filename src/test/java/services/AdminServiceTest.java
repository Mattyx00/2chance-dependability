package services;

import model.beans.Carrello;
import model.beans.Categoria;
import model.beans.Ordine;
import model.beans.Prodotto;
import model.beans.ProdottoCarrello;
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
import org.junit.jupiter.params.provider.NullAndEmptySource;
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
        // Arrange
        when(part.getSubmittedFileName()).thenReturn(null);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(new Prodotto(), new Categoria(), part, "{}"));
        assertTrue(exception.getMessage().contains("Image file name cannot be null"));
    }

    @Test
    @DisplayName("TF13: Should throw exception when Specifiche is invalid JSON")
    void shouldThrowExceptionWhenSpecificheIsInvalidJson() throws IOException {
        // Arrange
        String fileName = "img.jpg";
        byte[] imageRawStream = new byte[0];
        ByteArrayInputStream imageStream = new ByteArrayInputStream(imageRawStream);

        when(part.getSubmittedFileName()).thenReturn(fileName);
        when(part.getInputStream()).thenReturn(imageStream);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiProdotto(new Prodotto(), new Categoria(), part, "{invalid_json}"));
        assertTrue(exception.getMessage().contains("Invalid JSON format for specifiche"));
    }

    @Test
    @DisplayName("TF14: Should throw exception when getLastProduct returns invalid ID")
    void shouldThrowExceptionWhenLastProductIdIsInvalid() throws Exception {
        // Arrange
        Prodotto product = new Prodotto();
        Categoria category = new Categoria();
        String jsonSpecifiche = "{\"specifiche\":[]}";
        String fileName = "image.jpg";
        byte[] fakeImageRawStream = "test data".getBytes();
        ByteArrayInputStream fakeImageStream = new ByteArrayInputStream(fakeImageRawStream);

        when(part.getSubmittedFileName()).thenReturn(fileName);
        when(part.getInputStream()).thenReturn(fakeImageStream);
        when(prodottoDAO.getLastProduct()).thenReturn(-1);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> adminService.aggiungiProdotto(product, category, part, jsonSpecifiche));
        assertTrue(exception.getMessage().contains("Failed to retrieve the last added product ID."));
    }

    // =================================================================================================
    // mostraProdotti Tests
    // =================================================================================================

    @Test
    @DisplayName("TF15: Should return JSON when products exist")
    void shouldReturnJsonWhenProductsExist() throws Exception {
        // Arrange
        Categoria category = new Categoria();
        category.setNomeCategoria("Cat");

        Prodotto product = new Prodotto();
        product.setId(1);
        product.setMarca("Marca");
        product.setModello("Modello");
        product.setPrezzo(10.0f);
        product.setCategoria(category);

        ArrayList<Prodotto> arrayProducts = new ArrayList<>();
        arrayProducts.add(product);

        when(prodottoDAO.getProdotti()).thenReturn(arrayProducts);

        // Act
        String json = adminService.mostraProdotti();

        // Assert
        assertTrue(json.contains("\"prodotti\":"));
        assertTrue(json.contains("\"marca\":\"Marca\""));
    }

    @Test
    @DisplayName("TF16: Should throw exception when DAO returns null")
    void shouldThrowExceptionWhenDaoReturnsNullForProdotti() throws Exception {
        // Arrange
        when(prodottoDAO.getProdotti()).thenReturn(null);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> adminService.mostraProdotti());
        assertTrue(exception.getMessage().contains("DAO returned null for prodotti list"));
    }

    @Test
    @DisplayName("TF17: Should handle null elements in product list")
    void shouldHandleNullElementsInProductList() throws Exception {
        // Arrange
        Prodotto product = new Prodotto();
        product.setId(1);

        ArrayList<Prodotto> arrayProducts = new ArrayList<>();
        arrayProducts.add(null);
        arrayProducts.add(product);

        when(prodottoDAO.getProdotti()).thenReturn(arrayProducts);

        // Act
        String json = adminService.mostraProdotti();

        // Assert
        assertTrue(json.contains("\"prodotti\":"));
    }

    // =================================================================================================
    // eliminaProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("TF18: Should delete product when ID is positive")
    void shouldEliminaProdottoWhenIdIsPositive() throws Exception {
        // Arrange
        int positiveId = 10;

        // Act
        adminService.eliminaProdotto(positiveId);

        // Assert
        verify(prodottoDAO).eliminaProdotto(positiveId);
    }

    @ParameterizedTest
    @DisplayName("TF19, TF20: Should throw exception when ID is invalid")
    @ValueSource(ints = { 0, -1 })
    void shouldThrowExceptionWhenEliminaProdottoIdIsInvalid(int id) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.eliminaProdotto(id));
        assertTrue(exception.getMessage().contains("Product ID must be greater than 0"));
    }

    // =================================================================================================
    // mostraCategorie Tests
    // =================================================================================================

    @Test
    @DisplayName("TF21: Should return JSON when categories exist")
    void shouldReturnJsonWhenCategoriesExist() throws Exception {
        // Arrange
        String categoryName = "TestCat";
        Categoria category = new Categoria();
        category.setNomeCategoria(categoryName);

        ArrayList<Categoria> arrayCategories = new ArrayList<>();
        arrayCategories.add(category);

        when(categoriaDAO.getCategorie()).thenReturn(arrayCategories);

        // Act
        String json = adminService.mostraCategorie();

        // Assert
        assertTrue(json.contains(categoryName));
    }

    @Test
    @DisplayName("TF22: Should throw exception when DAO returns null for categories")
    void shouldThrowExceptionWhenCategoriaDaoReturnsNull() throws Exception {
        // Arrange
        when(categoriaDAO.getCategorie()).thenReturn(null);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> adminService.mostraCategorie());
        assertTrue(exception.getMessage().contains("DAO returned null for categorie list"));
    }

    // =================================================================================================
    // aggiungiCategoria Tests
    // =================================================================================================

    @Test
    @DisplayName("TF23: Should add category when name is valid")
    void shouldAddCategoriaWhenNameIsValid() throws Exception {
        // Arrange
        String validName = "NewCat";

        // Act
        adminService.aggiungiCategoria(validName);

        // Assert
        verify(categoriaDAO).addCategoria(any(Categoria.class));
    }

    @ParameterizedTest
    @NullAndEmptySource
    @DisplayName("TF24, TF25: Should throw exception when category name is invalid")
    void shouldThrowExceptionWhenCategoriaNameIsInvalid(String nameCategory) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.aggiungiCategoria(nameCategory));
        assertTrue(exception.getMessage().contains("Categoria name cannot be null or empty"));
    }

    // =================================================================================================
    // eliminaCategoria Tests
    // =================================================================================================

    @Test
    @DisplayName("TF26: Should delete category when name is valid")
    void shouldEliminaCategoriaWhenNameIsValid() throws Exception {
        // Arrange
        String validName = "OldCat";

        // Act
        adminService.eliminaCategoria(validName);

        // Assert
        verify(categoriaDAO).eliminaCategoria(validName);
    }

    @ParameterizedTest
    @NullAndEmptySource
    @DisplayName("TF27, TF28: Should throw exception when category name is invalid for deletion")
    void shouldThrowExceptionWhenEliminaCategoriaNameIsInvalid(String nameCategory) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.eliminaCategoria(nameCategory));
        assertTrue(exception.getMessage().contains("Categoria name cannot be null or empty"));
    }

    // =================================================================================================
    // mostraUtenti Tests
    // =================================================================================================

    @Test
    @DisplayName("TF29: Should return JSON when users exist")
    void shouldReturnJsonWhenUtentiExist() throws Exception {
        // Arrange
        Utente user = new Utente();
        user.setNome("Mario");
        user.setCognome("Rossi");

        ArrayList<Utente> arrayUsers = new ArrayList<>();
        arrayUsers.add(user);

        when(utenteDAO.getUtenti()).thenReturn(arrayUsers);

        // Act
        String json = adminService.mostraUtenti();

        // Assert
        assertAll(
                () -> assertTrue(json.contains("Mario")),
                () -> assertTrue(json.contains("Rossi")));
    }

    @Test
    @DisplayName("TF30: Should throw exception when DAO returns null for users")
    void shouldThrowExceptionWhenUtenteDaoReturnsNull() throws Exception {
        // Arrange
        when(utenteDAO.getUtenti()).thenReturn(null);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> adminService.mostraUtenti());
        assertTrue(exception.getMessage().contains("DAO returned null for utenti list"));
    }

    // =================================================================================================
    // mostraOrdini Tests
    // =================================================================================================

    @Test
    @DisplayName("TF31: Should return JSON when orders exist")
    void shouldReturnJsonWhenOrdiniExist() throws Exception {
        // Arrange
        Ordine order = new Ordine();
        order.setId(1);

        ArrayList<Ordine> arrayOrders = new ArrayList<>();
        arrayOrders.add(order);

        when(ordineDAO.getOrdini()).thenReturn(arrayOrders);

        // Act
        String json = adminService.mostraOrdini();

        // Assert
        assertTrue(json.contains("\"ordini\":"));
    }

    @Test
    @DisplayName("TF32: Should throw exception when DAO returns null for orders")
    void shouldThrowExceptionWhenOrdineDaoReturnsNull() throws Exception {
        // Arrange
        when(ordineDAO.getOrdini()).thenReturn(null);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> adminService.mostraOrdini());
        assertTrue(exception.getMessage().contains("DAO returned null for ordini list"));
    }

    // =================================================================================================
    // infoOrdine Tests
    // =================================================================================================

    @Test
    @DisplayName("TF33: Should return detailed JSON when order and cart exist")
    void shouldReturnInfoOrdineWhenOrderExists() throws Exception {
        // Arrange
        int idOrder = 1;
        Ordine order = new Ordine();
        order.setId(idOrder);

        Prodotto product = new Prodotto();
        product.setId(10);
        product.setPrezzo(100f);

        ProdottoCarrello productCart = new ProdottoCarrello();
        productCart.setProdotto(product);
        productCart.setQuantita(2);

        ArrayList<ProdottoCarrello> arrayProducts = new ArrayList<>();
        arrayProducts.add(productCart);

        Carrello cart = mock(Carrello.class);

        when(cart.getProdotti()).thenReturn(arrayProducts);
        when(cart.getTotaleCarrello()).thenReturn(200.0);

        when(ordineDAO.getOrdineById(idOrder)).thenReturn(order);
        when(ordineDAO.getProdottoOrdine(order)).thenReturn(cart);

        // Act
        String json = adminService.infoOrdine(idOrder);

        // Assert
        assertAll(
                () -> assertTrue(json.contains("\"prodotti\":")),
                () -> assertTrue(json.contains("100")));
    }

    @ParameterizedTest
    @DisplayName("TF34, TF35: Should throw exception when order ID is invalid")
    @ValueSource(ints = { 0, -1 })
    void shouldThrowExceptionWhenInfoOrdineIdIsInvalid(int id) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.infoOrdine(id));
        assertTrue(exception.getMessage().contains("Order ID must be non-null and positive"));
    }

    @Test
    @DisplayName("TF34 (Null): Should throw exception when order ID is null")
    void shouldThrowExceptionWhenInfoOrdineIdIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.infoOrdine(null));
        assertTrue(exception.getMessage().contains("Order ID must be non-null and positive"));
    }

    @Test
    @DisplayName("TF36: Should throw exception when order not found")
    void shouldThrowExceptionWhenOrderNotFound() throws Exception {
        // Arrange
        when(ordineDAO.getOrdineById(999)).thenReturn(null);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.infoOrdine(999));
        assertTrue(exception.getMessage().contains("Order not found"));
    }

    @Test
    @DisplayName("TF37: Should throw exception when cart is null")
    void shouldThrowExceptionWhenCartIsNull() throws Exception {
        // Arrange
        Ordine order = new Ordine();

        when(ordineDAO.getOrdineById(1)).thenReturn(order);
        when(ordineDAO.getProdottoOrdine(order)).thenReturn(null);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> adminService.infoOrdine(1));
        assertTrue(exception.getMessage().contains("Cart associated with order is null"));
    }

    // =================================================================================================
    // getProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("TF38: Should return JSON when product exists")
    void shouldReturnJsonWhenProductExists() throws Exception {
        // Arrange
        int idProduct = 1;
        String brandProduct = "Sony";
        String modelProduct = "PS5";

        Prodotto product = new Prodotto();
        product.setId(idProduct);
        product.setMarca(brandProduct);
        product.setModello(modelProduct);

        when(prodottoDAO.getProdottoById(idProduct)).thenReturn(product);

        // Act
        String json = adminService.getProdotto(idProduct);

        // Assert
        assertAll(
                () -> assertTrue(json.contains(brandProduct)),
                () -> assertTrue(json.contains(modelProduct)));
    }

    @ParameterizedTest
    @DisplayName("TF39, TF40: Should throw exception when product ID is invalid")
    @ValueSource(ints = { 0, -1 })
    void shouldThrowExceptionWhenGetProdottoIdIsInvalid(int id) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.getProdotto(id));
        assertTrue(exception.getMessage().contains("Product ID must be non-null and positive"));
    }

    @Test
    @DisplayName("TF39 (Null): Should throw exception when product ID is null")
    void shouldThrowExceptionWhenGetProdottoIdIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.getProdotto(null));
        assertTrue(exception.getMessage().contains("Product ID must be non-null and positive"));
    }

    @Test
    @DisplayName("TF41: Should throw exception when product not found")
    void shouldThrowExceptionWhenProductNotFound() throws Exception {
        // Arrange
        when(prodottoDAO.getProdottoById(999)).thenReturn(null);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.getProdotto(999));
        assertTrue(exception.getMessage().contains("Product not found"));
    }

    // =================================================================================================
    // modificaProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("TF42: Should modify product when inputs are valid and image provided")
    void shouldModificaProdottoWhenInputsAreValid() throws Exception {
        // Arrange
        Prodotto product = new Prodotto();
        product.setId(1);

        Categoria category = new Categoria();

        String jsonSpecifications = "{\"specifiche\":[{\"nome\":\"A\",\"valore\":\"B\"}]}";

        long imageSize = 100L;
        String imageFileName = "image.jpg";
        byte[] imageRawStream = "data".getBytes();
        ByteArrayInputStream imageStream = new ByteArrayInputStream(imageRawStream);

        when(part.getSize()).thenReturn(imageSize);
        when(part.getSubmittedFileName()).thenReturn(imageFileName);
        when(part.getInputStream()).thenReturn(imageStream);

        doNothing().when(prodottoDAO).modificaProdotto(product);
        when(prodottoDAO.eliminaSpecificheProdotto(anyInt())).thenReturn(1);
        doNothing().when(prodottoDAO).aggiungiSpecifiche(any(), eq(1));

        // Act
        adminService.modificaProdotto(product, category, part, jsonSpecifications);

        // Assert
        verify(prodottoDAO).modificaProdotto(product);
        verify(prodottoDAO).eliminaSpecificheProdotto(1);
        verify(prodottoDAO).aggiungiSpecifiche(any(), eq(1));
    }

    @Test
    @DisplayName("TF43: Should modify product when image is null (no image update)")
    void shouldModificaProdottoWhenImageIsNull() throws Exception {
        // Arrange
        Prodotto product = new Prodotto();
        product.setId(1);

        Categoria category = new Categoria();

        String jsonSpecifications = "{\"specifiche\":[]}";

        // Act
        adminService.modificaProdotto(product, category, null, jsonSpecifications);

        // Assert
        verify(prodottoDAO).modificaProdotto(product);
        verify(prodottoDAO).eliminaSpecificheProdotto(1);
        verify(prodottoDAO).aggiungiSpecifiche(any(), eq(1));
    }

    @Test
    @DisplayName("TF44: Should throw exception when Prodotto is null (modifica)")
    void shouldThrowExceptionWhenModificaProdottoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.modificaProdotto(null, new Categoria(), part, "{}"));
        assertTrue(exception.getMessage().contains("Prodotto cannot be null"));
    }

    @Test
    @DisplayName("TF45: Should throw exception when Categoria is null (modifica)")
    void shouldThrowExceptionWhenModificaCategoriaIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.modificaProdotto(new Prodotto(), null, part, "{}"));
        assertTrue(exception.getMessage().contains("Categoria cannot be null"));
    }

    @Test
    @DisplayName("TF46: Should throw exception when Specifiche is null (modifica)")
    void shouldThrowExceptionWhenModificaSpecificheIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.modificaProdotto(new Prodotto(), new Categoria(), part, null));
        assertTrue(exception.getMessage().contains("Specifiche string cannot be null"));
    }

    @Test
    @DisplayName("TF47: Should throw exception when Specifiche is invalid JSON (modifica)")
    void shouldThrowExceptionWhenModificaSpecificheIsInvalidJson() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> adminService.modificaProdotto(new Prodotto(), new Categoria(), part, "{invalid"));
        assertTrue(exception.getMessage().contains("Invalid JSON"));
    }
}
