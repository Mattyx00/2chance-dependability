package model.beans;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ProdottoCarrelloTest {

    private Prodotto defaultProdotto;

    @BeforeEach
    void setUp() {
        // Initialize a valid Prodotto generic instance for tests that require a
        // non-null product
        defaultProdotto = createValidProdotto(10.0);
    }

    // Helper method to create a Prodotto with a specific price
    private Prodotto createValidProdotto(double prezzo) {
        Prodotto p = new Prodotto();
        p.setPrezzo(prezzo);
        return p;
    }

    // --- Constructor Tests ---

    // F01: Prodotto is Null, Quantita is Valid -> IllegalArgumentException
    @Test
    @DisplayName("Constructor: Should throw IllegalArgumentException when Prodotto is null")
    void shouldThrowExceptionWhenProdottoIsNull_Constructor() {
        // Arrange
        Prodotto p = null;
        int q = 1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            new ProdottoCarrello(p, q);
        });
        assertEquals("Il prodotto non può essere null", exception.getMessage());
    }

    // F02: Prodotto is Valid, Quantita is Negative -> IllegalArgumentException
    @Test
    @DisplayName("Constructor: Should throw IllegalArgumentException when Quantita is negative")
    void shouldThrowExceptionWhenQuantitaIsNegative_Constructor() {
        // Arrange
        Prodotto p = defaultProdotto;
        int q = -1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            new ProdottoCarrello(p, q);
        });
        assertEquals("La quantità non può essere negativa", exception.getMessage());
    }

    // F03: Prodotto is Valid, Quantita is Zero -> Success
    @Test
    @DisplayName("Constructor: Should create object successfully when Quantita is zero")
    void shouldCreateObjectWhenQuantitaIsZero() {
        // Arrange
        Prodotto p = defaultProdotto;
        int q = 0;

        // Act
        ProdottoCarrello pc = new ProdottoCarrello(p, q);

        // Assert
        assertAll("Verify object creation with zero quantity",
                () -> assertNotNull(pc),
                () -> assertEquals(p, pc.getProdotto()),
                () -> assertEquals(0, pc.getQuantita()));
    }

    // F04: Prodotto is Valid, Quantita is Positive -> Success
    @Test
    @DisplayName("Constructor: Should create object successfully when Quantita is positive")
    void shouldCreateObjectWhenQuantitaIsPositive() {
        // Arrange
        Prodotto p = defaultProdotto;
        int q = 5;

        // Act
        ProdottoCarrello pc = new ProdottoCarrello(p, q);

        // Assert
        assertAll("Verify object creation with positive quantity",
                () -> assertNotNull(pc),
                () -> assertEquals(p, pc.getProdotto()),
                () -> assertEquals(5, pc.getQuantita()));
    }

    // --- setProdotto Tests ---

    // F05: Prodotto is Null -> IllegalArgumentException
    @Test
    @DisplayName("setProdotto: Should throw IllegalArgumentException when setting null Prodotto")
    void shouldThrowExceptionWhenSettingNullProdotto() {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello(); // Default constructor

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            pc.setProdotto(null);
        });
        Assertions.assertEquals("Il prodotto non può essere null", exception.getMessage());
    }

    // F06: Prodotto is Valid -> Success
    @Test
    @DisplayName("setProdotto: Should update Prodotto when valid")
    void shouldUpdateProdottoWhenValid() {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello();
        Prodotto newProdotto = createValidProdotto(20.0);

        // Act
        pc.setProdotto(newProdotto);

        // Assert
        assertEquals(newProdotto, pc.getProdotto());
    }

    // --- setQuantita Tests ---

    // F07: Quantita is Negative -> IllegalArgumentException
    @Test
    @DisplayName("setQuantita: Should throw IllegalArgumentException when setting negative Quantita")
    void shouldThrowExceptionWhenSettingNegativeQuantita() {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
            pc.setQuantita(-5);
        });
        assertEquals("La quantità non può essere negativa", exception.getMessage());
    }

    // F08, F09: Quantita is Valid (Zero or Positive) -> Success
    @ParameterizedTest
    @CsvSource({
            "0", // F08
            "1", // F09
            "100" // F09
    })
    @DisplayName("setQuantita: Should update Quantita when valid values provided")
    void shouldUpdateQuantitaWhenValidValuesProvided(int quantity) {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello();

        // Act
        pc.setQuantita(quantity);

        // Assert
        assertEquals(quantity, pc.getQuantita());
    }

    // --- getPrezzoTotale Tests ---

    // F10: Prodotto is Null -> IllegalStateException
    @Test
    @DisplayName("getPrezzoTotale: Should throw IllegalStateException when Prodotto is not set")
    void shouldThrowIllegalStateWhenProdottoNotSet_GetPrezzoTotale() {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello(); // Prodotto is null by default

        // Act & Assert
        IllegalStateException exception = assertThrows(IllegalStateException.class, () -> {
            pc.getPrezzoTotale();
        });
        assertEquals("Impossibile calcolare il prezzo totale: prodotto non impostato", exception.getMessage());
    }

    // F11-F13: Valid combinations of Price and Quantity -> Return correct total
    @ParameterizedTest(name = "Price: {0}, Quantity: {1} -> Expected: {2}")
    @CsvSource({
            "10.0, 2, 20.0", // F13: Positive price, Positive quantity
            "5.5, 0, 0.0", // F11: Positive price, Zero quantity
            "0.0, 5, 0.0", // F12: Zero price, Positive quantity
            "15.5, 3, 46.5" // F13 additional case
    })
    @DisplayName("getPrezzoTotale: Should calculate correct total")
    void shouldCalculateCorrectTotal(double price, int quantity, double expectedTotal) {
        // Arrange
        Prodotto p = createValidProdotto(price);
        ProdottoCarrello pc = new ProdottoCarrello(p, quantity);

        // Act
        double actualTotal = pc.getPrezzoTotale();

        // Assert
        assertEquals(expectedTotal, actualTotal, 0.001, "Total price calculation is incorrect");
    }
}
