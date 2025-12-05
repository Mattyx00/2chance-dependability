package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.Date;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Recensione class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Default constructor behavior
 * - Parameterized constructor with validation for all 5 parameters
 * - setValutazione() with boundary values (1-5)
 * - setDataRecensione(), setTesto(), setUtente(), setProdotto() with validation
 */
@DisplayName("Recensione Tests")
class RecensioneTest {

    // ========================================================================
    // Constructor Tests: Recensione()
    // ========================================================================

    @Test
    @DisplayName("Default constructor should create Recensione with null fields")
    void shouldCreateRecensioneWithDefaultConstructor() {
        // Arrange & Act
        Recensione recensione = new Recensione();

        // Assert
        assertNotNull(recensione, "Recensione instance should be created");
    }

    // ========================================================================
    // Constructor Tests: Recensione(Utente, Prodotto, int, String, Date)
    // ========================================================================

    @Test
    @DisplayName("Parameterized constructor should create Recensione when all parameters are valid")
    void shouldCreateRecensioneWhenAllParametersAreValid() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        int valutazione = 4;
        String testo = "Great product!";
        Date dataRecensione = new Date();

        // Act
        Recensione recensione = new Recensione(utente, prodotto, valutazione, testo, dataRecensione);

        // Assert
        assertNotNull(recensione, "Recensione should be created");
        assertEquals(utente, recensione.getUtente());
        assertEquals(prodotto, recensione.getProdotto());
        assertEquals(4, recensione.getValutazione());
        assertEquals("Great product!", recensione.getTesto());
        assertEquals(dataRecensione, recensione.getDataRecensione());
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when valutazione is zero")
    void shouldThrowExceptionWhenValutazioneIsZero() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(utente, prodotto, 0, "text", date),
                "Should throw exception for valutazione 0");
        assertTrue(exception.getMessage().contains("valutazione deve essere compresa tra 1 e 5"));
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when valutazione is six")
    void shouldThrowExceptionWhenValutazioneIsSix() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(utente, prodotto, 6, "text", date),
                "Should throw exception for valutazione 6");
        assertTrue(exception.getMessage().contains("valutazione deve essere compresa tra 1 e 5"));
    }

    @Test
    @DisplayName("Parameterized constructor should accept minimum valutazione of 1")
    void shouldAcceptMinimumValutazioneOfOne() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act
        Recensione recensione = new Recensione(utente, prodotto, 1, "Minimum rating", date);

        // Assert
        assertEquals(1, recensione.getValutazione(), "Valutazione should be 1 (boundary)");
    }

    @Test
    @DisplayName("Parameterized constructor should accept maximum valutazione of 5")
    void shouldAcceptMaximumValutazioneOfFive() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act
        Recensione recensione = new Recensione(utente, prodotto, 5, "Maximum rating", date);

        // Assert
        assertEquals(5, recensione.getValutazione(), "Valutazione should be 5 (boundary)");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when utente is null")
    void shouldThrowExceptionWhenUtenteIsNull() {
        // Arrange
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(null, prodotto, 3, "text", date),
                "Should throw exception for null utente");
        assertTrue(exception.getMessage().contains("utente non può essere null"));
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when prodotto is null")
    void shouldThrowExceptionWhenProdottoIsNull() {
        // Arrange
        Utente utente = createValidUtente();
        Date date = new Date();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(utente, null, 3, "text", date),
                "Should throw exception for null prodotto");
        assertTrue(exception.getMessage().contains("prodotto non può essere null"));
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when testo is null")
    void shouldThrowExceptionWhenTestoIsNull() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(utente, prodotto, 3, null, date),
                "Should throw exception for null testo");
        assertTrue(exception.getMessage().contains("testo della recensione non può essere null o vuoto"));
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when testo is empty")
    void shouldThrowExceptionWhenTestoIsEmpty() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> new Recensione(utente, prodotto, 3, "", date),
                "Should throw exception for empty testo");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when dataRecensione is null")
    void shouldThrowExceptionWhenDataRecensioneIsNull() {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Recensione(utente, prodotto, 3, "text", null),
                "Should throw exception for null dataRecensione");
        assertTrue(exception.getMessage().contains("data della recensione non può essere null"));
    }

    // ========================================================================
    // Parameterized Constructor Tests
    // ========================================================================

    @ParameterizedTest(name = "[{index}] valutazione={0}")
    @ValueSource(ints = { 1, 2, 3, 4, 5 })
    @DisplayName("Parameterized constructor should accept all valid valutazione values (1-5)")
    void shouldAcceptAllValidValutazioneValues(int valutazione) {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act & Assert
        assertDoesNotThrow(() -> {
            Recensione recensione = new Recensione(utente, prodotto, valutazione, "text", date);
            assertEquals(valutazione, recensione.getValutazione());
        }, "Should accept valutazione: " + valutazione);
    }

    @ParameterizedTest(name = "[{index}] invalid valutazione={0}")
    @ValueSource(ints = { -1, 0, 6, 7, 10 })
    @DisplayName("Parameterized constructor should reject invalid valutazione values")
    void shouldRejectInvalidValutazioneValues(int invalidValutazione) {
        // Arrange
        Utente utente = createValidUtente();
        Prodotto prodotto = createValidProdotto();
        Date date = new Date();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> new Recensione(utente, prodotto, invalidValutazione, "text", date),
                "Should reject invalid valutazione: " + invalidValutazione);
    }

    // ========================================================================
    // setValutazione() Tests
    // ========================================================================

    @Test
    @DisplayName("setValutazione should set valid valutazione")
    void shouldSetValidValutazione() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act
        recensione.setValutazione(4);

        // Assert
        assertEquals(4, recensione.getValutazione(), "Valutazione should be updated to 4");
    }

    @Test
    @DisplayName("setValutazione should throw exception for valutazione less than 1")
    void shouldThrowExceptionWhenSettingValutazioneLessThanOne() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> recensione.setValutazione(0),
                "Should throw exception for valutazione 0");
    }

    @Test
    @DisplayName("setValutazione should throw exception for valutazione greater than 5")
    void shouldThrowExceptionWhenSettingValutazioneGreaterThanFive() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> recensione.setValutazione(6),
                "Should throw exception for valutazione 6");
    }

    // ========================================================================
    // setDataRecensione() Tests
    // ========================================================================

    @Test
    @DisplayName("setDataRecensione should set valid date")
    void shouldSetValidDataRecensione() {
        // Arrange
        Recensione recensione = createValidRecensione();
        Date newDate = new Date(System.currentTimeMillis() - 86400000); // Yesterday

        // Act
        recensione.setDataRecensione(newDate);

        // Assert
        assertEquals(newDate, recensione.getDataRecensione(), "DataRecensione should be updated");
    }

    @Test
    @DisplayName("setDataRecensione should throw exception when date is null")
    void shouldThrowExceptionWhenSettingNullDataRecensione() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> recensione.setDataRecensione(null),
                "Should throw exception for null date");
        assertTrue(exception.getMessage().contains("data della recensione non può essere null"));
    }

    // ========================================================================
    // setTesto() Tests
    // ========================================================================

    @Test
    @DisplayName("setTesto should set valid testo")
    void shouldSetValidTesto() {
        // Arrange
        Recensione recensione = createValidRecensione();
        String newTesto = "Updated review text";

        // Act
        recensione.setTesto(newTesto);

        // Assert
        assertEquals(newTesto, recensione.getTesto(), "Testo should be updated");
    }

    @Test
    @DisplayName("setTesto should throw exception when testo is null")
    void shouldThrowExceptionWhenSettingNullTesto() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> recensione.setTesto(null),
                "Should throw exception for null testo");
    }

    @Test
    @DisplayName("setTesto should throw exception when testo is empty")
    void shouldThrowExceptionWhenSettingEmptyTesto() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> recensione.setTesto(""),
                "Should throw exception for empty testo");
    }

    // ========================================================================
    // setUtente() and setProdotto() Tests
    // ========================================================================

    @Test
    @DisplayName("setUtente should set valid utente")
    void shouldSetValidUtente() {
        // Arrange
        Recensione recensione = createValidRecensione();
        Utente newUtente = createValidUtente();
        newUtente.setEmail("newemail@test.com");

        // Act
        recensione.setUtente(newUtente);

        // Assert
        assertEquals(newUtente, recensione.getUtente(), "Utente should be updated");
    }

    @Test
    @DisplayName("setUtente should throw exception when utente is null")
    void shouldThrowExceptionWhenSettingNullUtente() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> recensione.setUtente(null),
                "Should throw exception for null utente");
    }

    @Test
    @DisplayName("setProdotto should set valid prodotto")
    void shouldSetValidProdotto() {
        // Arrange
        Recensione recensione = createValidRecensione();
        Prodotto newProdotto = createValidProdotto();
        newProdotto.setId(999);

        // Act
        recensione.setProdotto(newProdotto);

        // Assert
        assertEquals(newProdotto, recensione.getProdotto(), "Prodotto should be updated");
    }

    @Test
    @DisplayName("setProdotto should throw exception when prodotto is null")
    void shouldThrowExceptionWhenSettingNullProdotto() {
        // Arrange
        Recensione recensione = createValidRecensione();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> recensione.setProdotto(null),
                "Should throw exception for null prodotto");
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    private Recensione createValidRecensione() {
        return new Recensione(
                createValidUtente(),
                createValidProdotto(),
                3,
                "Good product",
                new Date());
    }

    private Utente createValidUtente() {
        Utente utente = new Utente();
        utente.setEmail("test@test.com");
        utente.setPassword("Password123");
        utente.setNome("Mario");
        utente.setCognome("Rossi");
        utente.setSesso("M");
        return utente;
    }

    private Prodotto createValidProdotto() {
        Prodotto prodotto = new Prodotto();
        prodotto.setId(1);
        prodotto.setModello("TestModel");
        prodotto.setMarca("TestBrand");
        prodotto.setDescrizione("Test Description");
        prodotto.setPrezzo(10.0);
        prodotto.setPeso(1.0);
        prodotto.setQuantitaProdotto(10);
        return prodotto;
    }
}
