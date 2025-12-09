package model.beans;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.Date;

import static org.junit.jupiter.api.Assertions.*;

class RecensioneTest {

    private Utente validUser;
    private Prodotto validProduct;
    private Date validDate;
    private int validRating;
    private String validText;
    private Recensione feedback;

    @BeforeEach
    void setUp() {
        validUser = new Utente();
        validProduct = new Prodotto();
        validDate = new Date();
        validRating = 3;
        validText = "Valid Text";
        feedback = new Recensione(validUser, validProduct, validRating, validText, validDate);
    }

    // --- Constructor Tests ---

    @Test
    @DisplayName("F1: Valid Construction - Should create Recensione when all inputs are valid")
    void shouldCreateRecensioneWhenAllInputsAreValid() {
        // Act
        Recensione newFeedback = new Recensione(validUser, validProduct, validRating, validText, validDate);

        // Assert
        assertAll("Constructor verification",
                () -> assertNotNull(newFeedback),
                () -> assertEquals(validUser, newFeedback.getUtente()),
                () -> assertEquals(validProduct, newFeedback.getProdotto()),
                () -> assertEquals(validRating, newFeedback.getValutazione()),
                () -> assertEquals(validText, newFeedback.getTesto()),
                () -> assertEquals(validDate, newFeedback.getDataRecensione()));
    }

    @Test
    @DisplayName("F2: Invalid Utente (Null) - Should throw exception")
    void shouldThrowExceptionWhenUtenteIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(null, validProduct, validRating, validText, validDate));
        assertEquals("L'utente non può essere null", exception.getMessage());
    }

    @Test
    @DisplayName("F3: Invalid Prodotto (Null) - Should throw exception")
    void shouldThrowExceptionWhenProdottoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(validUser, null, validRating, validText, validDate));
        assertEquals("Il prodotto non può essere null", exception.getMessage());
    }

    @ParameterizedTest
    @ValueSource(ints = { 0, 6, -1, 10 })
    @DisplayName("F4, F5: Invalid Valutazione (Out of range) - Should throw exception")
    void parameterizedShouldThrowExceptionWhenValutazioneIsInvalid(int invalidRating) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(validUser, validProduct, invalidRating, validText, validDate));
        assertEquals("La valutazione deve essere compresa tra 1 e 5", exception.getMessage());
    }

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F6, F7, F8: Invalid Testo (Null/Empty/Blank) - Should throw exception")
    void parameterizedShouldThrowExceptionWhenTestoIsInvalid(String invalidText) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(validUser, validProduct, validRating, invalidText, validDate));
        assertEquals("Il testo della recensione non può essere null o vuoto", exception.getMessage());
    }

    @Test
    @DisplayName("F9: Invalid DataRecensione (Null) - Should throw exception")
    void shouldThrowExceptionWhenDataRecensioneIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(validUser, validProduct, validRating, validText, null));
        assertEquals("La data della recensione non può essere null", exception.getMessage());
    }

    // --- Setter Tests ---

    @ParameterizedTest
    @ValueSource(ints = { 1, 3, 5 })
    @DisplayName("F10: Set Valid Rating - Should update field")
    void parameterizedShouldSetRatingWhenValid(int validRating) {
        // Act
        feedback.setValutazione(validRating);

        // Assert
        assertEquals(validRating, feedback.getValutazione());
    }

    @ParameterizedTest
    @ValueSource(ints = { 0, 6, -5, 10 })
    @DisplayName("F11, F12: Set Invalid Rating (Out of range) - Should throw exception")
    void parameterizedShouldThrowExceptionWhenSetRatingIsInvalid(int invalidRating) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> feedback.setValutazione(invalidRating));
        assertEquals("La valutazione deve essere compresa tra 1 e 5", exception.getMessage());
    }

    @Test
    @DisplayName("F13: Set Valid Text - Should update field")
    void shouldSetTextWhenValid() {
        // Arrange
        String newText = "Excellent";

        // Act
        feedback.setTesto(newText);

        // Assert
        assertEquals(newText, feedback.getTesto());
    }

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F14, F15: Set Invalid Text (Null/Empty/Blank) - Should throw exception")
    void parameterizedShouldThrowExceptionWhenSetTextIsInvalid(String invalidText) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> feedback.setTesto(invalidText));
        assertEquals("Il testo della recensione non può essere null o vuoto", exception.getMessage());
    }

    @Test
    @DisplayName("F16: Set Valid Utente - Should update field")
    void shouldSetUtenteWhenValid() {
        // Arrange
        Utente newUser = new Utente();

        // Act
        feedback.setUtente(newUser);

        // Assert
        assertEquals(newUser, feedback.getUtente());
    }

    @Test
    @DisplayName("F17: Set Invalid Utente (Null) - Should throw exception")
    void shouldThrowExceptionWhenSetUtenteIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> feedback.setUtente(null));
        assertEquals("L'utente non può essere null", exception.getMessage());
    }

    @Test
    @DisplayName("F18: Set Valid Prodotto - Should update field")
    void shouldSetProductWhenValid() {
        // Arrange
        Prodotto newProduct = new Prodotto();

        // Act
        feedback.setProdotto(newProduct);

        // Assert
        assertEquals(newProduct, feedback.getProdotto());
    }

    @Test
    @DisplayName("F19: Set Invalid Prodotto (Null) - Should throw exception")
    void shouldThrowExceptionWhenSetProductIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> feedback.setProdotto(null));
        assertEquals("Il prodotto non può essere null", exception.getMessage());
    }

    @Test
    @DisplayName("F20: Set Valid Date - Should update field")
    void shouldSetDateWhenValid() {
        // Arrange
        Date newDate = new Date();

        // Act
        feedback.setDataRecensione(newDate);

        // Assert
        assertEquals(newDate, feedback.getDataRecensione());
    }

    @Test
    @DisplayName("F21: Set Invalid Date (Null) - Should throw exception")
    void shouldThrowExceptionWhenSetDateIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> feedback.setDataRecensione(null));
        assertEquals("La data della recensione non può essere null", exception.getMessage());
    }
}
