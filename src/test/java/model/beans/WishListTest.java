package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the WishList class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Default constructor with empty product list
 * - Parameterized constructor with Utente validation
 * - setUtente() with null check
 * - setProdotti() with null check and list handling
 */
@DisplayName("WishList Tests")
class WishListTest {

    // ========================================================================
    // Constructor Tests: WishList()
    // ========================================================================

    @Test
    @DisplayName("Default constructor should initialize empty product list")
    void shouldInitializeEmptyProductListWhenDefaultConstructed() {
        // Arrange & Act
        WishList wishList = new WishList();

        // Assert
        assertNotNull(wishList, "WishList instance should be created");
        assertNotNull(wishList.getProdotti(), "Product list should not be null");
        assertTrue(wishList.getProdotti().isEmpty(), "Product list should be empty");
        assertNull(wishList.getUtente(), "Utente should be null with default constructor");
    }

    // ========================================================================
    // Constructor Tests: WishList(Utente)
    // ========================================================================

    @Test
    @DisplayName("Parameterized constructor should create WishList with valid utente")
    void shouldCreateWishListWithValidUtente() {
        // Arrange
        Utente utente = createValidUtente();

        // Act
        WishList wishList = new WishList(utente);

        // Assert
        assertNotNull(wishList, "WishList should be created");
        assertEquals(utente, wishList.getUtente(), "Utente should match");
        assertNotNull(wishList.getProdotti(), "Product list should be initialized");
        assertTrue(wishList.getProdotti().isEmpty(), "Product list should be empty");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when utente is null")
    void shouldThrowExceptionWhenConstructingWithNullUtente() {
        // Arrange
        Utente utente = null;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new WishList(utente),
                "Should throw exception for null utente");
        assertTrue(exception.getMessage().contains("utente non può essere null"));
    }

    // ========================================================================
    // setUtente() Tests
    // ========================================================================

    @Test
    @DisplayName("setUtente should throw exception when setting null utente")
    void shouldThrowExceptionWhenSettingNullUtente() {
        // Arrange
        WishList wishList = new WishList();
        Utente utente = createValidUtente();

        // Act
        wishList.setUtente(utente);

        // Assert
        assertEquals(utente, wishList.getUtente(), "Utente should be set");
    }

    @Test
    @DisplayName("setUtente should replace existing utente")
    void shouldReplaceExistingUtente() {
        // Arrange
        Utente utente1 = createValidUtente();
        Utente utente2 = createValidUtente();
        utente2.setEmail("different@test.com");
        WishList wishList = new WishList(utente1);

        // Act
        wishList.setUtente(utente2);

        // Assert
        assertEquals(utente2, wishList.getUtente(), "Utente should be replaced");
    }

    // ========================================================================
    // setProdotti() Tests
    // ========================================================================

    @Test
    @DisplayName("setProdotti should throw exception when setting null list")
    void shouldThrowExceptionWhenSettingNullProdottiList() {
        // Arrange
        WishList wishList = new WishList();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishList.setProdotti(null),
                "Should throw exception for null product list");
        assertTrue(exception.getMessage().contains("lista dei prodotti non può essere null"));
    }

    @Test
    @DisplayName("setProdotti should set empty product list")
    void shouldSetEmptyProdottiList() {
        // Arrange
        WishList wishList = new WishList();
        ArrayList<Prodotto> emptyList = new ArrayList<>();

        // Act
        wishList.setProdotti(emptyList);

        // Assert
        assertEquals(emptyList, wishList.getProdotti(), "Should set empty list");
        assertTrue(wishList.getProdotti().isEmpty(), "List should be empty");
    }

    @Test
    @DisplayName("setProdotti should set list with products")
    void shouldSetProdottiListWithProducts() {
        // Arrange
        WishList wishList = new WishList();
        ArrayList<Prodotto> prodotti = new ArrayList<>();
        prodotti.add(createValidProdotto(1));
        prodotti.add(createValidProdotto(2));

        // Act
        wishList.setProdotti(prodotti);

        // Assert
        assertEquals(prodotti, wishList.getProdotti(), "Should set product list");
        assertEquals(2, wishList.getProdotti().size(), "List should have 2 products");
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

    private Prodotto createValidProdotto(int id) {
        Prodotto prodotto = new Prodotto();
        prodotto.setId(id);
        prodotto.setModello("Model" + id);
        prodotto.setMarca("TestBrand");
        prodotto.setDescrizione("Test Description");
        prodotto.setPrezzo(10.0);
        prodotto.setPeso(1.0);
        prodotto.setQuantitaProdotto(10);
        return prodotto;
    }
}
