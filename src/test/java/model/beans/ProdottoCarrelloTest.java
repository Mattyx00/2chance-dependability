package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the ProdottoCarrello class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Default constructor behavior
 * - Parameterized constructor with various product/quantity combinations
 * - setProdotto() and getProdotto()
 * - setQuantita() and getQuantita() with boundary values
 * - getPrezzoTotale() calculation with various states
 */
@DisplayName("ProdottoCarrello Tests")
class ProdottoCarrelloTest {

    // ========================================================================
    // Constructor Tests: ProdottoCarrello()
    // ========================================================================

    @Test
    @DisplayName("Default constructor should create ProdottoCarrello with null product")
    void shouldCreateProdottoCarrelloWithDefaultConstructor() {
        // Arrange & Act
        ProdottoCarrello pc = new ProdottoCarrello();

        // Assert
        assertNotNull(pc, "ProdottoCarrello instance should be created");
        assertNull(pc.getProdotto(), "Product should be null with default constructor");
    }

    // ========================================================================
    // Constructor Tests: ProdottoCarrello(Prodotto, int)
    // ========================================================================

    @Test
    @DisplayName("Parameterized constructor should create ProdottoCarrello when both parameters are valid")
    void shouldCreateProdottoCarrelloWhenBothParametersAreValid() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        int quantita = 5;

        // Act
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, quantita);

        // Assert
        assertNotNull(pc, "ProdottoCarrello should be created");
        assertEquals(prodotto, pc.getProdotto(), "Product should match");
        assertEquals(5, pc.getQuantita(), "Quantity should be 5");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when prodotto is null")
    void shouldThrowExceptionWhenProdottoIsNull() {
        // Arrange
        Prodotto prodotto = null;
        int quantita = 5;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new ProdottoCarrello(prodotto, quantita),
                "Should throw exception for null product");
        assertTrue(exception.getMessage().contains("prodotto non può essere null"),
                "Exception message should mention null product");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when quantita is negative")
    void shouldThrowExceptionWhenQuantitaIsNegative() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        int quantita = -1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new ProdottoCarrello(prodotto, quantita),
                "Should throw exception for negative quantity");
        assertTrue(exception.getMessage().contains("quantità non può essere negativa"),
                "Exception message should mention negative quantity");
    }

    @Test
    @DisplayName("Parameterized constructor should create ProdottoCarrello when quantita is zero (boundary)")
    void shouldCreateProdottoCarrelloWhenQuantitaIsZero() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        int quantita = 0;

        // Act
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, quantita);

        // Assert
        assertNotNull(pc, "ProdottoCarrello should be created");
        assertEquals(0, pc.getQuantita(), "Quantity should be 0 (valid boundary case)");
    }

    @Test
    @DisplayName("Parameterized constructor should create ProdottoCarrello when quantita is 1 (boundary)")
    void shouldCreateProdottoCarrelloWhenQuantitaIsOne() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        int quantita = 1;

        // Act
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, quantita);

        // Assert
        assertEquals(1, pc.getQuantita(), "Quantity should be 1 (minimum positive)");
    }

    // ========================================================================
    // Parameterized Constructor Tests
    // ========================================================================

    @ParameterizedTest(name = "[{index}] {0}: quantita={1}")
    @CsvSource({
            "Valid typical case, 5",
            "Boundary zero, 0",
            "Boundary one, 1",
            "Large quantity, 100"
    })
    @DisplayName("Parameterized constructor should handle valid quantities")
    void shouldHandleValidQuantitiesInConstructor(String scenario, int quantita) {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);

        // Act & Assert
        assertDoesNotThrow(() -> {
            ProdottoCarrello pc = new ProdottoCarrello(prodotto, quantita);
            assertEquals(quantita, pc.getQuantita(),
                    "Quantity should match for: " + scenario);
        });
    }

    // ========================================================================
    // setProdotto() Tests
    // ========================================================================

    @Test
    @DisplayName("setProdotto should throw exception when setting null product")
    void shouldThrowExceptionWhenSettingNullProdotto() {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> pc.setProdotto(null),
                "Should throw exception when setting null product");
        assertTrue(exception.getMessage().contains("prodotto non può essere null"));
    }

    @Test
    @DisplayName("setProdotto should set valid product")
    void shouldSetValidProdotto() {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello();
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);

        // Act
        pc.setProdotto(prodotto);

        // Assert
        assertEquals(prodotto, pc.getProdotto(), "Product should be set correctly");
    }

    @Test
    @DisplayName("setProdotto should replace existing product")
    void shouldReplaceExistingProdotto() {
        // Arrange
        Prodotto p1 = createValidProdotto(1, "Product1", 10.0);
        Prodotto p2 = createValidProdotto(2, "Product2", 20.0);
        ProdottoCarrello pc = new ProdottoCarrello(p1, 5);

        // Act
        pc.setProdotto(p2);

        // Assert
        assertEquals(p2, pc.getProdotto(), "Product should be replaced");
        assertEquals(2, pc.getProdotto().getId(), "New product ID should be 2");
    }

    // ========================================================================
    // setQuantita() Tests
    // ========================================================================

    @Test
    @DisplayName("setQuantita should throw exception when setting negative quantidade")
    void shouldThrowExceptionWhenSettingNegativeQuantita() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 5);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> pc.setQuantita(-1),
                "Should throw exception for negative quantity");
        assertTrue(exception.getMessage().contains("quantità non può essere negativa"));
        assertEquals(5, pc.getQuantita(), "Quantity should remain unchanged after exception");
    }

    @Test
    @DisplayName("setQuantita should set quantity to zero (boundary)")
    void shouldSetQuantitaToZeroWhenValid() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 5);

        // Act
        pc.setQuantita(0);

        // Assert
        assertEquals(0, pc.getQuantita(), "Quantity should be updated to 0");
    }

    @Test
    @DisplayName("setQuantita should update quantity to new positive value")
    void shouldUpdateQuantitaToNewPositiveValue() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 5);

        // Act
        pc.setQuantita(10);

        // Assert
        assertEquals(10, pc.getQuantita(), "Quantity should be updated to 10");
    }

    @Test
    @DisplayName("setQuantita should update from zero to positive")
    void shouldUpdateQuantitaFromZeroToPositive() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 0);

        // Act
        pc.setQuantita(7);

        // Assert
        assertEquals(7, pc.getQuantita(), "Quantity should be updated from 0 to 7");
    }

    // ========================================================================
    // getPrezzoTotale() Tests
    // ========================================================================

    @Test
    @DisplayName("getPrezzoTotale should throw exception when prodotto is null")
    void shouldThrowExceptionWhenCalculatingPrezzoTotaleWithNullProdotto() {
        // Arrange
        ProdottoCarrello pc = new ProdottoCarrello();

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> pc.getPrezzoTotale(),
                "Should throw exception when calculating price with null product");
        assertTrue(exception.getMessage().contains("Impossibile calcolare il prezzo totale"),
                "Exception message should mention calculation issue");
    }

    @Test
    @DisplayName("getPrezzoTotale should return zero when quantita is zero")
    void shouldReturnZeroWhenQuantitaIsZero() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 0);

        // Act
        double total = pc.getPrezzoTotale();

        // Assert
        assertEquals(0.0, total, 0.001, "Total should be 0 when quantity is 0");
    }

    @Test
    @DisplayName("getPrezzoTotale should calculate correct total for single item")
    void shouldCalculateCorrectTotalForSingleItem() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 1);

        // Act
        double total = pc.getPrezzoTotale();

        // Assert
        assertEquals(10.0, total, 0.001, "Total should be 10.0 (10.0 * 1)");
    }

    @Test
    @DisplayName("getPrezzoTotale should calculate correct total for multiple items")
    void shouldCalculateCorrectTotalForMultipleItems() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 5);

        // Act
        double total = pc.getPrezzoTotale();

        // Assert
        assertEquals(50.0, total, 0.001, "Total should be 50.0 (10.0 * 5)");
    }

    @Test
    @DisplayName("getPrezzoTotale should return zero for free product with multiple items")
    void shouldReturnZeroForFreeProductWithMultipleItems() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "FreeProduct", 0.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 10);

        // Act
        double total = pc.getPrezzoTotale();

        // Assert
        assertEquals(0.0, total, 0.001, "Total should be 0 for free product");
    }

    @Test
    @DisplayName("getPrezzoTotale should calculate correct total with decimal price")
    void shouldCalculateCorrectTotalWithDecimalPrice() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 9.99);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 3);

        // Act
        double total = pc.getPrezzoTotale();

        // Assert
        assertEquals(29.97, total, 0.01, "Total should be 29.97 (9.99 * 3)");
    }

    // ========================================================================
    // Parameterized getPrezzoTotale() Tests
    // ========================================================================

    @ParameterizedTest(name = "[{index}] {0}: price={1}, qty={2}, expected={3}")
    @CsvSource({
            "Zero quantity, 10.0, 0, 0.0",
            "Single item, 10.0, 1, 10.0",
            "Multiple items, 10.0, 5, 50.0",
            "Free product, 0.0, 5, 0.0",
            "Decimal price, 9.99, 3, 29.97"
    })
    @DisplayName("getPrezzoTotale should calculate correctly for various inputs")
    void shouldCalculatePrezzoTotaleCorrectly(String scenario, double price, int quantity, double expected) {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", price);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, quantity);

        // Act
        double total = pc.getPrezzoTotale();

        // Assert
        assertEquals(expected, total, 0.01, "Total should match expected for: " + scenario);
    }

    // ========================================================================
    // Integration Tests
    // ========================================================================

    @Test
    @DisplayName("Should update total price when quantity is changed")
    void shouldUpdateTotalPriceWhenQuantityChanged() {
        // Arrange
        Prodotto prodotto = createValidProdotto(1, "TestProduct", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 2);
        assertEquals(20.0, pc.getPrezzoTotale(), 0.001, "Initial total should be 20.0");

        // Act
        pc.setQuantita(5);

        // Assert
        assertEquals(50.0, pc.getPrezzoTotale(), 0.001,
                "Total should be updated to 50.0 after quantity change");
    }

    @Test
    @DisplayName("Should update total price when product is changed")
    void shouldUpdateTotalPriceWhenProductChanged() {
        // Arrange
        Prodotto p1 = createValidProdotto(1, "Product1", 10.0);
        Prodotto p2 = createValidProdotto(2, "Product2", 20.0);
        ProdottoCarrello pc = new ProdottoCarrello(p1, 3);
        assertEquals(30.0, pc.getPrezzoTotale(), 0.001, "Initial total should be 30.0");

        // Act
        pc.setProdotto(p2);

        // Assert
        assertEquals(60.0, pc.getPrezzoTotale(), 0.001,
                "Total should be updated to 60.0 after product change");
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    /**
     * Helper method to create a valid Prodotto instance for testing.
     */
    private Prodotto createValidProdotto(int id, String modello, double prezzo) {
        Prodotto prodotto = new Prodotto();
        prodotto.setId(id);
        prodotto.setModello(modello);
        prodotto.setMarca("TestBrand");
        prodotto.setDescrizione("Test Description");
        prodotto.setPrezzo(prezzo);
        prodotto.setPeso(1.0);
        prodotto.setQuantitaProdotto(100);
        return prodotto;
    }
}
