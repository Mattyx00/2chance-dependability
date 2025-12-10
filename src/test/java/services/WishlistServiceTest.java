package services;

import model.beans.Prodotto;
import model.beans.Utente;
import model.beans.WishList;
import model.dao.ProdottoDAO;
import model.dao.WishListDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class WishlistServiceTest {

    private WishListDAO wishListDAO;
    private ProdottoDAO prodottoDAO;
    private WishlistService service;

    @BeforeEach
    void setUp() {
        wishListDAO = mock(WishListDAO.class);
        prodottoDAO = mock(ProdottoDAO.class);
        service = new WishlistService(wishListDAO, prodottoDAO);
    }

    // --------------------------------------------------------------------------------
    // 1. Constructor: WishlistService(WishListDAO wishListDAO, ProdottoDAO
    // prodottoDAO)
    // --------------------------------------------------------------------------------

    // F1: wishListDAO is null
    @Test
    @DisplayName("Constructor should throw exception when wishListDAO is null")
    void shouldThrowExceptionWhenWishListDaoIsNull() {
        // Arrange
        ProdottoDAO validProdottoDAO = mock(ProdottoDAO.class);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            new WishlistService(null, validProdottoDAO);
        });
        assertEquals("WishListDAO cannot be null", exception.getMessage());
    }

    // F2: prodottoDAO is null
    @Test
    @DisplayName("Constructor should throw exception when prodottoDAO is null")
    void shouldThrowExceptionWhenProdottoDaoIsNull() {
        // Arrange
        WishListDAO validWishListDAO = mock(WishListDAO.class);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            new WishlistService(validWishListDAO, null);
        });
        assertEquals("ProdottoDAO cannot be null", exception.getMessage());
    }

    // F3: Both dependencies are valid
    @Test
    @DisplayName("Constructor should initialize successfully when dependencies are valid")
    void shouldInitializeWhenDependenciesAreValid() {
        // Arrange
        WishListDAO validWishListDAO = mock(WishListDAO.class);
        ProdottoDAO validProdottoDAO = mock(ProdottoDAO.class);

        // Act
        WishlistService validService = new WishlistService(validWishListDAO, validProdottoDAO);

        // Assert
        assertNotNull(validService, "Service instance should not be null");
    }

    // --------------------------------------------------------------------------------
    // 2. Method: void addToWishList(Utente utente, int idProdotto)
    // --------------------------------------------------------------------------------

    // F1: utente is null
    @Test
    @DisplayName("addToWishList should throw exception when utente is null")
    void shouldThrowExceptionWhenUtenteIsNullInAddToWishList() {
        // Arrange
        Utente utente = null;
        int idProdotto = 1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            service.addToWishList(utente, idProdotto);
        });
        assertEquals("Utente cannot be null", exception.getMessage());
    }

    // F2, F3: idProdotto is zero or negative (Invalid)
    @ParameterizedTest
    @DisplayName("addToWishList should throw exception when productId is invalid")
    @ValueSource(ints = { 0, -1, -50 })
    void shouldThrowExceptionWhenProductIdIsInvalid(int invalidId) {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            service.addToWishList(utente, invalidId);
        });
        assertTrue(exception.getMessage().contains("Product ID must be positive"));
    }

    // F4: Product does not exist
    @Test
    @DisplayName("addToWishList should throw exception when product does not exist")
    void shouldThrowExceptionWhenProductNotFound() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        int nonExistentId = 999;
        when(prodottoDAO.getProdottoById(nonExistentId)).thenReturn(null);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            service.addToWishList(utente, nonExistentId);
        });
        assertEquals("Product not found with ID: " + nonExistentId, exception.getMessage());
    }

    // F5: Product lookup throws SQLException
    @Test
    @DisplayName("addToWishList should propagate SQLException when product lookup fails")
    void shouldPropagateSQLExceptionWhenProductLookupFails() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        int idProdotto = 1;
        when(prodottoDAO.getProdottoById(idProdotto)).thenThrow(new SQLException("DB Error"));

        // Act & Assert
        assertThrows(SQLException.class, () -> {
            service.addToWishList(utente, idProdotto);
        });
    }

    // F6: Successful addition
    @Test
    @DisplayName("addToWishList should match the provided populated list")
    void shouldCallDaoWhenAddingValidProduct() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        int idProdotto = 1;
        Prodotto product = new Prodotto();
        when(prodottoDAO.getProdottoById(idProdotto)).thenReturn(product);

        // Act
        service.addToWishList(utente, idProdotto);

        // Assert
        verify(wishListDAO).addToWishList(utente, product);
    }

    // F7: Add operation throws SQLException
    @Test
    @DisplayName("addToWishList should propagate SQLException when add operation fails")
    void shouldPropagateSQLExceptionWhenAddOperationFails() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        int idProdotto = 1;
        Prodotto product = new Prodotto();
        when(prodottoDAO.getProdottoById(idProdotto)).thenReturn(product);
        doThrow(new SQLException("Insertion Error")).when(wishListDAO).addToWishList(utente, product);

        // Act & Assert
        assertThrows(SQLException.class, () -> {
            service.addToWishList(utente, idProdotto);
        });
    }

    // --------------------------------------------------------------------------------
    // 3. Method: WishList getWishListByUser(Utente utente)
    // --------------------------------------------------------------------------------

    // F1: utente is null
    @Test
    @DisplayName("getWishListByUser should throw exception when utente is null")
    void shouldThrowExceptionWhenUtenteIsNullInGetWishList() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            service.getWishListByUser(null);
        });
        assertEquals("Utente cannot be null", exception.getMessage());
    }

    // F2: Successful retrieval
    @Test
    @DisplayName("getWishListByUser should return WishList when user is valid")
    void shouldReturnWishListWhenUserIsValid() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        WishList expectedWishList = new WishList();
        when(wishListDAO.getWishListByUser(utente)).thenReturn(expectedWishList);

        // Act
        WishList result = service.getWishListByUser(utente);

        // Assert
        assertEquals(expectedWishList, result);
    }

    // F3: DB Error during retrieval
    @Test
    @DisplayName("getWishListByUser should propagate SQLException when retrieval fails")
    void shouldPropagateSQLExceptionWhenRetrievalFails() throws SQLException {
        // Arrange
        Utente utente = new Utente();
        when(wishListDAO.getWishListByUser(utente)).thenThrow(new SQLException("Retrieval Error"));

        // Act & Assert
        assertThrows(SQLException.class, () -> {
            service.getWishListByUser(utente);
        });
    }

    // --------------------------------------------------------------------------------
    // 4. Method: void removeFromWishList(int idUtente, int idProdotto)
    // --------------------------------------------------------------------------------

    // F1, F2: idUtente is zero or negative (Invalid)
    @ParameterizedTest
    @DisplayName("removeFromWishList should throw exception when userId is invalid")
    @ValueSource(ints = { 0, -1, -5 })
    void shouldThrowExceptionWhenUserIdIsInvalid(int invalidUserId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            service.removeFromWishList(invalidUserId, 1);
        });
        assertTrue(exception.getMessage().contains("User ID must be positive"));
    }

    // F3, F4: idProdotto is zero or negative (Invalid)
    @ParameterizedTest
    @DisplayName("removeFromWishList should throw exception when productId is invalid")
    @ValueSource(ints = { 0, -1, -5 })
    void shouldThrowExceptionWhenProductIdIsInvalidInRemove(int invalidProductId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            service.removeFromWishList(1, invalidProductId);
        });
        assertTrue(exception.getMessage().contains("Product ID must be positive"));
    }

    // F5: Successful removal
    @Test
    @DisplayName("removeFromWishList should call DAO when inputs are valid")
    void shouldCallDaoWhenRemovingValidProduct() throws SQLException {
        // Arrange
        int idUtente = 1;
        int idProdotto = 1;

        // Act
        service.removeFromWishList(idUtente, idProdotto);

        // Assert
        verify(wishListDAO).removeFromWishList(idUtente, idProdotto);
    }

    // F6: DB Error during removal
    @Test
    @DisplayName("removeFromWishList should propagate SQLException when removal fails")
    void shouldPropagateSQLExceptionWhenRemovalFails() throws SQLException {
        // Arrange
        int idUtente = 1;
        int idProdotto = 1;
        doThrow(new SQLException("Removal Error")).when(wishListDAO).removeFromWishList(idUtente, idProdotto);

        // Act & Assert
        assertThrows(SQLException.class, () -> {
            service.removeFromWishList(idUtente, idProdotto);
        });
    }
}
