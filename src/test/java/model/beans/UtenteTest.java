package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Utente class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - String setters (setNome, setCognome, setEmail, setTelefono) with null/empty
 * validation
 * - setPassword() with hashing behavior
 * - Collection setters (setOrdini, setRecensioni) with null check
 * - getOrdineIndex() with various ordini list states
 */
@DisplayName("Utente Tests")
class UtenteTest {

    @Test
    @DisplayName("Default constructor should create Utente")
    void shouldCreateUtenteWithDefaultConstructor() {
        // Arrange & Act
        Utente utente = new Utente();

        // Assert
        assertNotNull(utente, "Utente instance should be created");
    }

    // ========================================================================
    // String Setter Tests (setNome, setCognome, setEmail, setTelefono)
    // ========================================================================

    @Test
    @DisplayName("setNome should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullNome() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setNome(null));
    }

    @Test
    @DisplayName("setNome should throw exception when setting empty")
    void shouldThrowExceptionWhenSettingEmptyNome() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setNome(""));
    }

    @Test
    @DisplayName("setNome should set valid name")
    void shouldSetValidNome() {
        // Arrange
        Utente utente = new Utente();

        // Act
        utente.setNome("Mario");

        // Assert
        assertEquals("Mario", utente.getNome());
    }

    @Test
    @DisplayName("setCognome should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullCognome() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setCognome(null));
    }

    @Test
    @DisplayName("setCognome should set valid cognome")
    void shouldSetValidCognome() {
        // Arrange
        Utente utente = new Utente();

        // Act
        utente.setCognome("Rossi");

        // Assert
        assertEquals("Rossi", utente.getCognome());
    }

    @Test
    @DisplayName("setEmail should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullEmail() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setEmail(null));
    }

    @Test
    @DisplayName("setEmail should set valid email")
    void shouldSetValidEmail() {
        // Arrange
        Utente utente = new Utente();

        // Act
        utente.setEmail("test@test.com");

        // Assert
        assertEquals("test@test.com", utente.getEmail());
    }

    @Test
    @DisplayName("setTelefono should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullTelefono() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setTelefono(null));
    }

    @Test
    @DisplayName("setTelefono should set valid phone number")
    void shouldSetValidTelefono() {
        // Arrange
        Utente utente = new Utente();

        // Act
        utente.setTelefono("1234567890");

        // Assert
        assertEquals("1234567890", utente.getTelefono());
    }

    // ========================================================================
    // setPassword() Tests
    // ========================================================================

    @Test
    @DisplayName("setPassword should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullPassword() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setPassword(null));
    }

    @Test
    @DisplayName("setPassword should throw exception when setting empty")
    void shouldThrowExceptionWhenSettingEmptyPassword() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setPassword(""));
    }

    @Test
    @DisplayName("setPassword should hash password when setting valid password")
    void shouldHashPasswordWhenSettingValidPassword() {
        // Arrange
        Utente utente = new Utente();
        String password = "myPassword123";

        // Act
        utente.setPassword(password);

        // Assert
        assertNotNull(utente.getPasswordHash(), "PasswordHash should not be null");
        assertNotEquals(password, utente.getPasswordHash(), "Password should be hashed");
        assertTrue(utente.getPasswordHash().length() > 0, "PasswordHash should have content");
    }

    // ========================================================================
    // Collection Setter Tests
    // ========================================================================

    @Test
    @DisplayName("setOrdini should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullOrdini() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setOrdini(null));
    }

    @Test
    @DisplayName("setOrdini should set empty list")
    void shouldSetEmptyOrdiniList() {
        // Arrange
        Utente utente = new Utente();
        ArrayList<Ordine> ordini = new ArrayList<>();

        // Act
        utente.setOrdini(ordini);

        // Assert
        assertEquals(ordini, utente.getOrdini());
        assertTrue(utente.getOrdini().isEmpty());
    }

    @Test
    @DisplayName("setRecensioni should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullRecensioni() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.setRecensioni(null));
    }

    @Test
    @DisplayName("setRecensioni should set empty list")
    void shouldSetEmptyRecensioniList() {
        // Arrange
        Utente utente = new Utente();
        ArrayList<Recensione> recensioni = new ArrayList<>();

        // Act
        utente.setRecensioni(recensioni);

        // Assert
        assertEquals(recensioni, utente.getRecensioni());
    }

    // ========================================================================
    // getOrdineIndex() Tests
    // ========================================================================

    @Test
    @DisplayName("getOrdineIndex should throw exception when searching for null ordine")
    void shouldThrowExceptionWhenSearchingForNullOrdine() {
        // Arrange
        Utente utente = new Utente();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> utente.getOrdineIndex(null));
    }

    @Test
    @DisplayName("getOrdineIndex should return -1 when ordini list is null")
    void shouldReturnNegativeOneWhenOrdiniListIsNull() {
        // Arrange
        Utente utente = new Utente();
        Ordine ordine = createValidOrdine(1);

        // Act
        int index = utente.getOrdineIndex(ordine);

        // Assert
        assertEquals(-1, index, "Should return -1 when ordini is null");
    }

    @Test
    @DisplayName("getOrdineIndex should return -1 when ordini list is empty")
    void shouldReturnNegativeOneWhenOrdiniListIsEmpty() {
        // Arrange
        Utente utente = new Utente();
        utente.setOrdini(new ArrayList<>());
        Ordine ordine = createValidOrdine(1);

        // Act
        int index = utente.getOrdineIndex(ordine);

        // Assert
        assertEquals(-1, index, "Should return -1 when ordini is empty");
    }

    @Test
    @DisplayName("getOrdineIndex should return correct index when ordine is found")
    void shouldReturnCorrectIndexWhenOrdineIsFound() {
        // Arrange
        Utente utente = new Utente();
        Ordine ordine1 = createValidOrdine(1);
        Ordine ordine2 = createValidOrdine(2);
        ArrayList<Ordine> ordini = new ArrayList<>();
        ordini.add(ordine1);
        ordini.add(ordine2);
        utente.setOrdini(ordini);

        // Act
        int index = utente.getOrdineIndex(ordine2);

        // Assert
        assertEquals(1, index, "Should return index 1 for ordine2");
    }

    @Test
    @DisplayName("getOrdineIndex should return -1 when ordine not in list")
    void shouldReturnNegativeOneWhenOrdineNotInList() {
        // Arrange
        Utente utente = new Utente();
        Ordine ordine1 = createValidOrdine(1);
        Ordine ordine2 = createValidOrdine(2);
        Ordine ordine3 = createValidOrdine(3);
        ArrayList<Ordine> ordini = new ArrayList<>();
        ordini.add(ordine1);
        ordini.add(ordine2);
        utente.setOrdini(ordini);

        // Act
        int index = utente.getOrdineIndex(ordine3);

        // Assert
        assertEquals(-1, index, "Should return -1 when ordine not in list");
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    private Ordine createValidOrdine(int id) {
        Ordine ordine = new Ordine();
        ordine.setId(id);
        return ordine;
    }
}
