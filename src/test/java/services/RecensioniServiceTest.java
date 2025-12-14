package services;

import model.beans.Prodotto;
import model.beans.Recensione;
import model.beans.Utente;
import model.dao.ProdottoDAO;
import model.dao.RecensioneDAO;
import model.dao.UtenteDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class RecensioniServiceTest {

    @Mock
    private RecensioneDAO recensioneDAO;
    @Mock
    private ProdottoDAO prodottoDAO;
    @Mock
    private UtenteDAO utenteDAO;

    @InjectMocks
    private RecensioniService recensioniService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("C4: Should instantiate service when all DAOs are non-null")
    void shouldInitializeSuccessfullyWhenAllDAOsAreValid() {
        // Act & Assert
        assertNotNull(recensioniService);
    }

    @Test
    @DisplayName("C1: Should throw exception when RecensioneDAO is null")
    void shouldThrowExceptionWhenRecensioneDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new RecensioniService(null, prodottoDAO, utenteDAO));
        assertEquals("RecensioneDAO cannot be null", exception.getMessage());
    }

    @Test
    @DisplayName("C2: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenProdottoDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new RecensioniService(recensioneDAO, null, utenteDAO));
        assertEquals("ProdottoDAO cannot be null", exception.getMessage());
    }

    @Test
    @DisplayName("C3: Should throw exception when UtenteDAO is null")
    void shouldThrowExceptionWhenUtenteDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new RecensioniService(recensioneDAO, prodottoDAO, null));
        assertEquals("UtenteDAO cannot be null", exception.getMessage());
    }

    // =================================================================================================
    // aggiungiRecensione Tests
    // =================================================================================================

    @Test
    @DisplayName("AR1: Should throw exception when Utente is null")
    void shouldThrowExceptionWhenUtenteIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.aggiungiRecensione(null, "Testo Recensione", 5, 1));
        assertEquals("Utente cannot be null", exception.getMessage());
    }

    @ParameterizedTest(name = "AR2, AR3, AR4: Should throw exception when review text is \"{0}\"")
    @NullAndEmptySource
    @DisplayName("AR2, AR3, AR4: Should throw exception when review text is invalid")
    void shouldThrowExceptionWhenTextIsInvalid(String testo) {
        // Arrange
        Utente utente = new Utente();
        int ratingProduct = 5;
        int productId = 1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.aggiungiRecensione(utente, testo, ratingProduct, productId));
        assertEquals("Review text cannot be null or empty", exception.getMessage());
    }

    @ParameterizedTest(name = "AR5, AR6: Should throw exception when rating is {0}")
    @ValueSource(ints = { 0, 6, -1, 10 })
    @DisplayName("AR5, AR6: Should throw exception when rating is invalid")
    void shouldThrowExceptionWhenRatingIsInvalid(int ratingProduct) {
        // Arrange
        Utente user = new Utente();
        String reviewText = "Recensione valida";
        int productId = 1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.aggiungiRecensione(user, reviewText, ratingProduct, productId));
        assertEquals("Rating must be between 1 and 5", exception.getMessage());
    }

    @Test
    @DisplayName("AR7: Should throw exception when idProdotto is invalid")
    void shouldThrowExceptionWhenProductIdIsInvalid() {
        // Arrange
        Utente user = new Utente();
        String reviewText = "Recensione valida";
        int ratingProduct = 5;
        int productId = -1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.aggiungiRecensione(user, reviewText, ratingProduct, productId));
        assertEquals("Product ID must be positive", exception.getMessage());
    }

    @Test
    @DisplayName("AR8: Should throw exception when Product is not found")
    void shouldThrowExceptionWhenProductNotFound() throws SQLException {
        // Arrange
        Utente user = new Utente();
        String reviewText = "Recensione valida";
        int ratingProduct = 5;
        int productId = 1;

        when(prodottoDAO.getProdottoById(productId)).thenReturn(null);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.aggiungiRecensione(user, reviewText, ratingProduct, productId));
        assertEquals("Product not found with ID: " + productId, exception.getMessage());
    }

    @Test
    @DisplayName("AR9: Should add review and return updated user when input is valid")
    void shouldAddReviewWhenInputIsValid() throws SQLException {
        // Arrange
        Utente expectedUser = new Utente();
        String reviewText = "Recensione valida";
        int ratingProduct = 5;
        int productId = 1;

        Prodotto product = new Prodotto();
        product.setId(productId);

        Recensione review = new Recensione();

        ArrayList<Recensione> arrayReviews = new ArrayList<>();
        arrayReviews.add(review);

        when(prodottoDAO.getProdottoById(productId)).thenReturn(product);
        when(recensioneDAO.addRecensione(any(Recensione.class))).thenReturn(1);
        when(recensioneDAO.getRecensioniByUtente(expectedUser)).thenReturn(arrayReviews);

        // Act
        Utente actualUser = recensioniService.aggiungiRecensione(expectedUser, reviewText, ratingProduct, productId);

        // Assert
        assertAll(
                () -> assertNotNull(actualUser),
                () -> assertNotNull(actualUser.getRecensioni()),
                () -> assertFalse(actualUser.getRecensioni().isEmpty()));

        verify(recensioneDAO).addRecensione(any(Recensione.class));
        verify(recensioneDAO).getRecensioniByUtente(expectedUser);
    }

    @Test
    @DisplayName("AR10: Should propagate SQLException from DAO")
    void shouldPropagateSQLExceptionFromDAO() throws SQLException {
        // Arrange
        Utente user = new Utente();
        String reviewText = "Recensione valida";
        int ratingProduct = 5;
        int productId = 1;

        when(prodottoDAO.getProdottoById(productId)).thenThrow(new SQLException("Database Error"));

        // Act & Assert
        SQLException exception = assertThrows(
                SQLException.class,
                () -> recensioniService.aggiungiRecensione(user, reviewText, ratingProduct, productId));
        assertEquals("Database Error", exception.getMessage());
    }

    // =================================================================================================
    // eliminaRecensione Tests
    // =================================================================================================

    @Test
    @DisplayName("ER1: Should throw exception when review ID is invalid")
    void shouldThrowExceptionWhenReviewIdIsInvalid() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.eliminaRecensione(-1, 1));
        assertEquals("Review ID must be positive", exception.getMessage());
    }

    @Test
    @DisplayName("ER2: Should throw exception when user ID is invalid")
    void shouldThrowExceptionWhenUserIdIsInvalid() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.eliminaRecensione(1, 0));
        assertEquals("User ID must be positive", exception.getMessage());
    }

    @Test
    @DisplayName("ER3: Should throw exception when user is not found")
    void shouldThrowExceptionWhenUserNotFound() throws SQLException {
        // Arrange
        int reviewId = 1;
        int userId = 1;

        when(utenteDAO.getUtenteById(userId)).thenReturn(null);
        doNothing().when(recensioneDAO).deleteRecensione(reviewId);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensioniService.eliminaRecensione(reviewId, userId));
        assertEquals("Utente not found with ID: " + userId, exception.getMessage());
    }

    @Test
    @DisplayName("ER4: Should delete review and return found Utente")
    void shouldDeleteReviewAndReturnUserWhenSuccessful() throws SQLException {
        // Arrange
        int reviewId = 1;
        int userId = 1;

        Utente expectedUtente = new Utente();
        expectedUtente.setId(userId);

        when(utenteDAO.getUtenteById(userId)).thenReturn(expectedUtente);
        doNothing().when(recensioneDAO).deleteRecensione(reviewId);

        // Act
        Utente actualUser = recensioniService.eliminaRecensione(reviewId, userId);

        // Assert
        assertAll(
                () -> assertNotNull(actualUser),
                () -> assertEquals(expectedUtente, actualUser));

        verify(recensioneDAO).deleteRecensione(reviewId);
        verify(utenteDAO).getUtenteById(userId);
    }

    @Test
    @DisplayName("ER5: Should propagate SQLException when DAO throws exception")
    void shouldPropagateSQLExceptionWhenDeletionFails() throws SQLException {
        // Arrange
        int reviewId = 1;
        int userId = 1;

        doThrow(new SQLException("Delete Failed")).when(recensioneDAO).deleteRecensione(reviewId);

        // Act & Assert
        SQLException exception = assertThrows(
                SQLException.class,
                () -> recensioniService.eliminaRecensione(reviewId, userId));
        assertEquals("Delete Failed", exception.getMessage());
    }
}
