package model.beans;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Carrello class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Constructor initialization
 * - getTotaleCarrello() with empty/single/multiple items
 * - aggiungiProdotto() with null checks and various cart states
 * - eliminaProdotto() with null checks, empty cart, existing/non-existing products
 * - cambiaQuantita() with null/invalid inputs and state exceptions
 */
@DisplayName("Carrello Tests")
class CarrelloTest {

    // ========================================================================
    // Constructor Tests: Carrello()
    // ========================================================================

    @Test
    @DisplayName("Constructor should initialize empty non-null product list")
    void shouldInitializeEmptyNonNullProductListWhenConstructed() {
        // Arrange & Act
        Carrello carrello = new Carrello();

        // Assert
        assertNotNull(carrello, "Carrello instance should be created");
        assertNotNull(carrello.getProdotti(), "Product list should not be null");
        assertTrue(carrello.getProdotti().isEmpty(), "Product list should be empty");
        assertEquals(0, carrello.getProdotti().size(), "Product list size should be 0");
    }

    // ========================================================================
    // getTotaleCarrello() Tests
    // ========================================================================

    @Test
    @DisplayName("getTotaleCarrello should return zero for empty cart")
    void shouldReturnZeroForEmptyCart() {
        // Arrange
        Carrello carrello = new Carrello();

        // Act
        double total = carrello.getTotaleCarrello();

        // Assert
        assertEquals(0.0, total, 0.001, "Empty cart should have zero total");
    }

    @Test
    @DisplayName("getTotaleCarrello should calculate correct total for single item")
    void shouldCalculateCorrectTotalForSingleItem() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 2); // total = 20.0
        carrello.aggiungiProdotto(pc);

        // Act
        double total = carrello.getTotaleCarrello();

        // Assert
        assertEquals(20.0, total, 0.001, "Cart total should be 20.0 (10.0 * 2)");
    }

    @Test
    @DisplayName("getTotaleCarrello should calculate correct total for multiple items")
    void shouldCalculateCorrectTotalForMultipleItems() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto p1 = createProdotto(1, "Product1", 10.0);
        Prodotto p2 = createProdotto(2, "Product2", 7.75);
        ProdottoCarrello pc1 = new ProdottoCarrello(p1, 2); // total = 20.0
        ProdottoCarrello pc2 = new ProdottoCarrello(p2, 2); // total = 15.5
        carrello.aggiungiProdotto(pc1);
        carrello.aggiungiProdotto(pc2);

        // Act
        double total = carrello.getTotaleCarrello();

        // Assert
        assertEquals(35.5, total, 0.01, "Cart total should be 35.5 (20.0 + 15.5)");
    }

    @Test
    @DisplayName("getTotaleCarrello should handle items with zero price")
    void shouldCalculateTotalWithZeroPriceItems() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto p1 = createProdotto(1, "FreeProduct", 0.0);
        Prodotto p2 = createProdotto(2, "PaidProduct", 10.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(p1, 5); // total = 0.0
        ProdottoCarrello pc2 = new ProdottoCarrello(p2, 3); // total = 30.0
        carrello.aggiungiProdotto(pc1);
        carrello.aggiungiProdotto(pc2);

        // Act
        double total = carrello.getTotaleCarrello();

        // Assert
        assertEquals(30.0, total, 0.001, "Cart total should be 30.0 (0.0 + 30.0)");
    }

    // ========================================================================
    // aggiungiProdotto() Tests
    // ========================================================================

    @Test
    @DisplayName("aggiungiProdotto should throw exception when adding null product")
    void shouldThrowExceptionWhenAddingNullProduct() {
        // Arrange
        Carrello carrello = new Carrello();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> carrello.aggiungiProdotto(null),
                "Should throw IllegalArgumentException when adding null"
        );
        assertTrue(exception.getMessage().contains("prodotto da aggiungere non può essere null"),
                "Exception message should mention null product");
    }

    @Test
    @DisplayName("aggiungiProdotto should add product to empty cart")
    void shouldAddProductToEmptyCart() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 2);

        // Act
        boolean result = carrello.aggiungiProdotto(pc);

        // Assert
        assertTrue(result, "aggiungiProdotto should return true");
        assertEquals(1, carrello.getProdotti().size(), "Cart should have 1 item");
        assertTrue(carrello.getProdotti().contains(pc), "Cart should contain the added product");
    }

    @Test
    @DisplayName("aggiungiProdotto should add multiple different products to cart")
    void shouldAddMultipleProductsToCart() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto p1 = createProdotto(1, "Product1", 10.0);
        Prodotto p2 = createProdotto(2, "Product2", 15.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(p1, 2);
        ProdottoCarrello pc2 = new ProdottoCarrello(p2, 1);

        // Act
        carrello.aggiungiProdotto(pc1);
        carrello.aggiungiProdotto(pc2);

        // Assert
        assertEquals(2, carrello.getProdotti().size(), "Cart should have 2 items");
        assertTrue(carrello.getProdotti().contains(pc1), "Cart should contain first product");
        assertTrue(carrello.getProdotti().contains(pc2), "Cart should contain second product");
    }

    @Test
    @DisplayName("aggiungiProdotto should allow adding duplicate product (same ID)")
    void shouldAllowAddingDuplicateProduct() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(prodotto, 2);
        ProdottoCarrello pc2 = new ProdottoCarrello(prodotto, 3);

        // Act
        carrello.aggiungiProdotto(pc1);
        carrello.aggiungiProdotto(pc2);

        // Assert
        assertEquals(2, carrello.getProdotti().size(), 
                "Cart should allow duplicate products (ArrayList behavior)");
    }

    // ========================================================================
    // eliminaProdotto() Tests
    // ========================================================================

    @Test
    @DisplayName("eliminaProdotto should throw exception when removing null product")
    void shouldThrowExceptionWhenRemovingNullProduct() {
        // Arrange
        Carrello carrello = new Carrello();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> carrello.eliminaProdotto(null),
                "Should throw IllegalArgumentException when removing null"
        );
        assertTrue(exception.getMessage().contains("prodotto da eliminare non può essere null"),
                "Exception message should mention null product");
    }

    @Test
    @DisplayName("eliminaProdotto should do nothing when removing from empty cart")
    void shouldDoNothingWhenRemovingFromEmptyCart() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);

        // Act
        carrello.eliminaProdotto(prodotto);

        // Assert
        assertTrue(carrello.getProdotti().isEmpty(), "Cart should remain empty");
        assertEquals(0, carrello.getProdotti().size(), "Cart size should be 0");
    }

    @Test
    @DisplayName("eliminaProdotto should remove existing product from cart")
    void shouldRemoveExistingProductFromCart() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 2);
        carrello.aggiungiProdotto(pc);

        // Act
        carrello.eliminaProdotto(prodotto);

        // Assert
        assertTrue(carrello.getProdotti().isEmpty(), "Cart should be empty after removal");
        assertEquals(0, carrello.getProdotti().size(), "Cart size should be 0");
    }

    @Test
    @DisplayName("eliminaProdotto should do nothing when product not in cart")
    void shouldDoNothingWhenRemovingNonExistingProduct() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto p1 = createProdotto(1, "Product1", 10.0);
        Prodotto p2 = createProdotto(2, "Product2", 15.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(p1, 2);
        carrello.aggiungiProdotto(pc1);

        // Act
        carrello.eliminaProdotto(p2);

        // Assert
        assertEquals(1, carrello.getProdotti().size(), "Cart should still have 1 item");
        assertTrue(carrello.getProdotti().contains(pc1), "Original product should remain");
    }

    @Test
    @DisplayName("eliminaProdotto should remove all matching products by ID")
    void shouldRemoveAllMatchingProductsByIdFromCart() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(prodotto, 2);
        ProdottoCarrello pc2 = new ProdottoCarrello(prodotto, 3);
        carrello.aggiungiProdotto(pc1);
        carrello.aggiungiProdotto(pc2);

        // Act
        carrello.eliminaProdotto(prodotto);

        // Assert
        assertTrue(carrello.getProdotti().isEmpty(), 
                "All products with matching ID should be removed");
    }

    @Test
    @DisplayName("eliminaProdotto should only remove products with matching ID")
    void shouldRemoveOnlyMatchingProducts() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto p1 = createProdotto(1, "Product1", 10.0);
        Prodotto p2 = createProdotto(2, "Product2", 15.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(p1, 2);
        ProdottoCarrello pc2 = new ProdottoCarrello(p2, 1);
        carrello.aggiungiProdotto(pc1);
        carrello.aggiungiProdotto(pc2);

        // Act
        carrello.eliminaProdotto(p1);

        // Assert
        assertEquals(1, carrello.getProdotti().size(), "Cart should have 1 item");
        assertEquals(p2.getId(), carrello.getProdotti().get(0).getProdotto().getId(),
                "Remaining product should be p2");
    }

    // ========================================================================
    // cambiaQuantita() Tests
    // ========================================================================

    @Test
    @DisplayName("cambiaQuantita should throw exception when product is null")
    void shouldThrowExceptionWhenChangingQuantityWithNullProduct() {
        // Arrange
        Carrello carrello = new Carrello();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> carrello.cambiaQuantita(null, 5),
                "Should throw IllegalArgumentException for null product"
        );
        assertTrue(exception.getMessage().contains("prodotto non può essere null"),
                "Exception message should mention null product");
    }

    @Test
    @DisplayName("cambiaQuantita should throw exception when quantity is zero")
    void shouldThrowExceptionWhenChangingQuantityToZero() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> carrello.cambiaQuantita(prodotto, 0),
                "Should throw IllegalArgumentException for zero quantity"
        );
        assertTrue(exception.getMessage().contains("quantità deve essere maggiore di zero"),
 

    @Test
    @DisplayName("cambiaQuantita should throw exception when quantity is negative")
    void shouldThrowExceptionWhenChangingQuantityToNegative() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> carrello.cambiaQuantita(prodotto, -1),
                "Should throw IllegalArgumentException for negative quantity"
        );
        assertTrue(exception.getMessage().contains("quantità deve essere maggiore di zero"),
                "Exception message should mention quantity requirement");
    }

    @Test
    @DisplayName("cambiaQuantita should update quantity for existing product")
    void shouldUpdateQuantityForExistingProduct() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 2);
        carrello.aggiungiProdotto(pc);

        // Act
        carrello.cambiaQuantita(prodotto, 10);

        // Assert
        assertEquals(1, carrello.getProdotti().size(), "Cart should still have 1 item");
        assertEquals(10, carrello.getProdotti().get(0).getQuantita(),
                "Product quantity should be updated to 10");
    }

    @Test
    @DisplayName("cambiaQuantita should update quantity to 1 (minimum valid)")
    void shouldUpdateQuantityToMinimumValid() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc = new ProdottoCarrello(prodotto, 5);
        carrello.aggiungiProdotto(pc);

        // Act
        carrello.cambiaQuantita(prodotto, 1);

        // Assert
        assertEquals(1, carrello.getProdotti().get(0).getQuantita(),
                "Product quantity should be updated to 1");
    }

    @Test
    @DisplayName("cambiaQuantita should throw exception when product not in cart")
    void shouldThrowExceptionWhenChangingQuantityOfNonExistingProduct() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto p1 = createProdotto(1, "Product1", 10.0);
        Prodotto p2 = createProdotto(2, "Product2", 15.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(p1, 5);
        carrello.aggiungiProdotto(pc1);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> carrello.cambiaQuantita(p2, 10),
                "Should throw IllegalStateException when product not in cart"
        );
        assertTrue(exception.getMessage().contains("non è presente nel carrello"),
                "Exception message should mention product not in cart");
        assertTrue(exception.getMessage().contains("" + p2.getId()),
                "Exception message should mention product ID");
    }

    @Test
    @DisplayName("cambiaQuantita should throw exception for empty cart")
    void shouldThrowExceptionWhenChangingQuantityInEmptyCart() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> carrello.cambiaQuantita(prodotto, 5),
                "Should throw IllegalStateException for empty cart"
        );
        assertTrue(exception.getMessage().contains("non è presente nel carrello"),
                "Exception message should indicate product not found");
    }

    @Test
    @DisplayName("cambiaQuantita should update only first matching product when duplicates exist")
    void shouldUpdateFirstMatchingProductWhenDuplicatesExist() {
        // Arrange
        Carrello carrello = new Carrello();
        Prodotto prodotto = createProdotto(1, "Product1", 10.0);
        ProdottoCarrello pc1 = new ProdottoCarrello(prodotto, 2);
        ProdottoCarrello pc2 = new ProdottoCarrello(prodotto, 3);
        carrello.aggiungiProdotto(pc1);
        carrello.aggiungiProdotto(pc2);

        // Act
        carrello.cambiaQuantita(prodotto, 10);

        // Assert
        assertEquals(2, carrello.getProdotti().size(), "Cart should still have 2 items");
        assertEquals(10, carrello.getProdotti().get(0).getQuantita(),
                "First product quantity should be updated to 10");
        assertEquals(3, carrello.getProdotti().get(1).getQuantita(),
                "Second product quantity should remain 3");
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    /**
     * Helper method to create a Prodotto instance for testing.
     */
    private Prodotto createProdotto(int id, String modello, double prezzo) {
        Prodotto prodotto = new Prodotto();
        prodotto.setId(id);
        prodotto.setModello(modello);
        prodotto.setMarca("TestMarca");
        prodotto.setDescrizione("Test Description");
        prodotto.setPrezzo(prezzo);
        prodotto.setPeso(1.0);
        prodotto.setQuantitaProdotto(10);
        return prodotto;
    }
}
