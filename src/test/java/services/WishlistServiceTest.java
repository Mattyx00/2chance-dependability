package services;

import model.beans.Prodotto;
import model.beans.Utente;
import model.beans.WishList;
import model.dao.ProdottoDAO;
import model.dao.WishListDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class WishlistServiceTest {

    @Mock
    private WishListDAO wishListDAO;

    @Mock
    private ProdottoDAO prodottoDAO;

    @InjectMocks
    private WishlistService wishlistService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should throw exception when WishListDAO is null")
    void shouldThrowExceptionWhenWishListDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new WishlistService(null, prodottoDAO));
        assertEquals("WishListDAO cannot be null", exception.getMessage());
    }

    @Test
    @DisplayName("TF2: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenProdottoDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new WishlistService(wishListDAO, null));
        assertEquals("ProdottoDAO cannot be null", exception.getMessage());
    }

    @Test
    @DisplayName("TF3: Should instantiate service when all DAOs are valid")
    void shouldInstantiateServiceWhenAllDAOsAreValid() {
        // Act
        WishlistService service = new WishlistService(wishListDAO, prodottoDAO);

        // Assert
        assertNotNull(service);
    }

    // =================================================================================================
    // addToWishList Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should throw exception when Utente is null in addToWishList")
    void shouldThrowExceptionWhenUtenteIsNullInAddToWishList() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlistService.addToWishList(null, 1));
        assertEquals("Utente cannot be null", exception.getMessage());
    }

    @ParameterizedTest
    @DisplayName("TF2, TF3: Should throw exception when Product ID is invalid in addToWishList")
    @CsvSource({ "0", "-1", "-50" })
    void shouldThrowExceptionWhenProductIdIsInvalidInAddToWishList(int invalidId) {
        // Arrange
        Utente validUtente = new Utente();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlistService.addToWishList(validUtente, invalidId));
        assertTrue(exception.getMessage().contains("Product ID must be positive"));
    }

    @Test
    @DisplayName("TF4: Should throw exception when Product does not exist")
    void shouldThrowExceptionWhenProductDoesNotExist() throws SQLException {
        // Arrange
        Utente validUtente = new Utente();
        int nonExistentId = 999;

        when(prodottoDAO.getProdottoById(nonExistentId)).thenReturn(null);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlistService.addToWishList(validUtente, nonExistentId));
        assertTrue(exception.getMessage().contains("Product not found with ID: " + nonExistentId));
    }

    @Test
    @DisplayName("TF6: Should add product to wishlist when inputs are valid and product exists")
    void shouldAddProductToWishlistWhenInputsAreValidAndProductExists() throws SQLException {
        // Arrange
        Utente validUser = new Utente();

        int validProductId = 1;
        Prodotto product = new Prodotto();
        product.setId(validProductId);

        when(prodottoDAO.getProdottoById(validProductId)).thenReturn(product);
        doNothing().when(wishListDAO).addToWishList(validUser, product);

        // Act
        wishlistService.addToWishList(validUser, validProductId);

        // Assert
        verify(prodottoDAO).getProdottoById(validProductId);
        verify(wishListDAO).addToWishList(validUser, product);
    }

    // =================================================================================================
    // getWishListByUser Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should throw exception when Utente is null in getWishListByUser")
    void shouldThrowExceptionWhenUtenteIsNullInGetWishListByUser() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlistService.getWishListByUser(null));
        assertEquals("Utente cannot be null", exception.getMessage());
    }

    @Test
    @DisplayName("TF2: Should return WishList when user is valid")
    void shouldReturnWishListWhenUserIsValid() throws SQLException {
        // Arrange
        Utente validUser = new Utente();
        WishList expectedWishList = new WishList();
        when(wishListDAO.getWishListByUser(validUser)).thenReturn(expectedWishList);

        // Act
        WishList wishlist = wishlistService.getWishListByUser(validUser);

        // Assert
        assertAll(
                () -> assertNotNull(wishlist),
                () -> assertEquals(expectedWishList, wishlist));
        verify(wishListDAO).getWishListByUser(validUser);
    }

    // =================================================================================================
    // removeFromWishList Tests
    // =================================================================================================

    @ParameterizedTest
    @DisplayName("TF1, TF2: Should throw exception when User ID is invalid in removeFromWishList")
    @CsvSource({ "0", "-1", "-5" })
    void shouldThrowExceptionWhenUserIdIsInvalidInRemove(int invalidUserId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlistService.removeFromWishList(invalidUserId, 1)); // Assuming 1 is a valid product ID for
                                                                             // this checking
        assertTrue(exception.getMessage().contains("User ID must be positive"));
    }

    @ParameterizedTest
    @DisplayName("TF3, TF4: Should throw exception when Product ID is invalid in removeFromWishList")
    @CsvSource({ "0", "-1", "-5" })
    void shouldThrowExceptionWhenProductIdIsInvalidInRemove(int invalidProductId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlistService.removeFromWishList(1, invalidProductId)); // Assuming 1 is a valid user ID for
                                                                                // this checking
        assertTrue(exception.getMessage().contains("Product ID must be positive"));
    }

    @Test
    @DisplayName("TF5: Should remove product from wishlist when inputs are valid")
    void shouldRemoveProductFromWishlistWhenInputsAreValid() throws SQLException {
        // Arrange
        int validUserId = 1;
        int validProductId = 1;

        doNothing().when(wishListDAO).removeFromWishList(validUserId, validProductId);

        // Act
        wishlistService.removeFromWishList(validUserId, validProductId);

        // Assert
        verify(wishListDAO).removeFromWishList(validUserId, validProductId);
    }
}
