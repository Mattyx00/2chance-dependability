package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.Date;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Ordine class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Default constructor
 * - setDataOrdine() with null check
 * - setIndirizzo() with null/empty validation
 * - setPrezzoTotale() with boundary values (>= 0)
 * - setUt
 * 
 * ente() and setCarrello() with null checks
 */
@DisplayName("Ordine Tests")
class OrdineTest {

    @Test
    @DisplayName("Default constructor should create Ordine")
    void shouldCreateOrdineWithDefaultConstructor() {
        // Arrange & Act
        Ordine ordine = new Ordine();

        // Assert
        assertNotNull(ordine, "Ordine instance should be created");
    }

    // ========================================================================
    // setDataOrdine() Tests
    // ========================================================================

    @Test
    @DisplayName("setDataOrdine should throw exception when setting null date")
    void shouldThrowExceptionWhenSettingNullDataOrdine() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> ordine.setDataOrdine(null),
                "Should throw exception for null date");
        assertTrue(exception.getMessage().contains("data dell'ordine non può essere null"));
    }

    @Test
    @DisplayName("setDataOrdine should set valid date")
    void shouldSetValidDataOrdine() {
        // Arrange
        Ordine ordine = new Ordine();
        Date date = new Date();

        // Act
        ordine.setDataOrdine(date);

        // Assert
        assertEquals(date, ordine.getDataOrdine(), "DataOrdine should be set");
    }

    // ========================================================================
    // setIndirizzo() Tests
    // ========================================================================

    @Test
    @DisplayName("setIndirizzo should throw exception when setting null address")
    void shouldThrowExceptionWhenSettingNullIndirizzo() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> ordine.setIndirizzo(null),
                "Should throw exception for null indirizzo");
    }

    @Test
    @DisplayName("setIndirizzo should throw exception when setting empty address")
    void shouldThrowExceptionWhenSettingEmptyIndirizzo() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> ordine.setIndirizzo(""),
                "Should throw exception for empty indirizzo");
    }

    @Test
    @DisplayName("setIndirizzo should set valid address")
    void shouldSetValidIndirizzo() {
        // Arrange
        Ordine ordine = new Ordine();
        String indirizzo = "Via Roma 123, 80100 Napoli";

        // Act
        ordine.setIndirizzo(indirizzo);

        // Assert
        assertEquals(indirizzo, ordine.getIndirizzo(), "Indirizzo should be set");
    }

    // ========================================================================
    // setPrezzoTotale() Tests
    // ========================================================================

    @Test
    @DisplayName("setPrezzoTotale should throw exception when setting negative price")
    void shouldThrowExceptionWhenSettingNegativePrezzoTotale() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> ordine.setPrezzoTotale(-0.01),
                "Should throw exception for negative price");
        assertTrue(exception.getMessage().contains("prezzo totale non può essere negativo"));
    }

    @Test
    @DisplayName("setPrezzoTotale should set zero price (boundary)")
    void shouldSetZeroPrezzoTotale() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act
        ordine.setPrezzoTotale(0.0);

        // Assert
        assertEquals(0.0, ordine.getPrezzoTotale(), 0.001, "PrezzoTotale should be 0.0");
    }

    @Test
    @DisplayName("setPrezzoTotale should set positive price")
    void shouldSetPositivePrezzoTotale() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act
        ordine.setPrezzoTotale(99.99);

        // Assert
        assertEquals(99.99, ordine.getPrezzoTotale(), 0.01, "PrezzoTotale should be set");
    }

    // ========================================================================
    // setUtente() Tests
    // ========================================================================

    @Test
    @DisplayName("setUtente should throw exception when setting null utente")
    void shouldThrowExceptionWhenSettingNullUtente() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> ordine.setUtente(null),
                "Should throw exception for null utente");
    }

    @Test
    @DisplayName("setUtente should set valid utente")
    void shouldSetValidUtente() {
        // Arrange
        Ordine ordine = new Ordine();
        Utente utente = createValidUtente();

        // Act
        ordine.setUtente(utente);

        // Assert
        assertEquals(utente, ordine.getUtente(), "Utente should be set");
    }

    // ========================================================================
    // setCarrello() Tests
    // ========================================================================

    @Test
    @DisplayName("setCarrello should throw exception when setting null carrello")
    void shouldThrowExceptionWhenSettingNullCarrello() {
        // Arrange
        Ordine ordine = new Ordine();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> ordine.setCarrello(null),
                "Should throw exception for null carrello");
    }

    @Test
    @DisplayName("setCarrello should set valid carrello")
    void shouldSetValidCarrello() {
        // Arrange
        Ordine ordine = new Ordine();
        Carrello carrello = new Carrello();

        // Act
        ordine.setCarrello(carrello);

        // Assert
        assertEquals(carrello, ordine.getCarrello(), "Carrello should be set");
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    private Utente createValidUtente() {
        Utente utente = new Utente();
        utente.setEmail("test@test.com");
        utente.setPassword("Password123");
        utente.setNome("Mario");
        utente.setCognome("Rossi");
        return utente;
    }
}
